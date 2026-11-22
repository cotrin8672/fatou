use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use lsp_server::{Connection, Message, Notification, Request};
use serde_json::{Value, json};

struct Session {
    client: Connection,
    task: std::thread::JoinHandle<()>,
    next: i32,
}

fn uri(path: &Path) -> String {
    let path = path.to_string_lossy().replace('\\', "/");
    let path = path.strip_prefix("//?/").unwrap_or(&path);
    format!(
        "file://{}{}",
        if path.starts_with('/') { "" } else { "/" },
        path
    )
}

impl Session {
    fn start(root: &Path) -> Self {
        let (server, client) = Connection::memory();
        let task = std::thread::spawn(move || fatou::lsp::serve(&server).unwrap());
        let mut session = Self {
            client,
            task,
            next: 0,
        };
        let uri = uri(root);
        session.request(
            "initialize",
            json!({"processId":null,"rootUri":uri,
            "workspaceFolders":[{"uri":uri,"name":"script"}],"capabilities":{}}),
        );
        session.notify("initialized", json!({}));
        session
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        self.next += 1;
        let id = self.next.into();
        self.client
            .sender
            .send(Message::Request(Request::new(id, method.into(), params)))
            .unwrap();
        loop {
            let msg = self
                .client
                .receiver
                .recv_timeout(Duration::from_secs(10))
                .unwrap();
            if let Message::Response(r) = msg
                && r.id == self.next.into()
            {
                return r.response_result.expect("successful LSP response");
            }
        }
    }

    fn notify(&self, method: &str, params: Value) {
        self.client
            .sender
            .send(Message::Notification(Notification::new(
                method.into(),
                params,
            )))
            .unwrap();
    }

    fn open(&self, file: &Path, text: &str) {
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument":{"uri":uri(file),
                    "languageId":"julia", "version":1, "text":text}}),
        )
    }

    fn definition(&mut self, file: &Path, line: u32, character: u32) -> Value {
        self.request("textDocument/definition",json!({"textDocument":{"uri":uri(file)}, "position":{"line":line,"character":character}}))
    }

    fn await_definition(&mut self, file: &Path, line: u32, character: u32) -> Value {
        let until = Instant::now() + Duration::from_secs(5);
        loop {
            let result = self.definition(file, line, character);
            if !result.is_null() || Instant::now() >= until {
                return result;
            }
            std::thread::sleep(Duration::from_millis(30));
        }
    }

    fn finish(mut self) {
        self.request("shutdown", Value::Null);
        self.notify("exit", Value::Null);
        self.task.join().unwrap();
    }
}

fn write(root: &Path, leaf: &str, text: &str) -> PathBuf {
    let path = root.join(leaf);
    fs::write(&path, text).unwrap();
    path
}

#[test]
fn loose_script_jumps_via_static_chain_and_reads_unsaved_source() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    let main = write(&root, "main.jl", "include(\"one.jl\")\nhelper(1)\n");
    write(&root, "one.jl", "include(\"two.jl\")\n");
    let target = write(&root, "two.jl", "helper(x) = x\n");
    let mut lsp = Session::start(&root);
    lsp.open(&main, &fs::read_to_string(&main).unwrap());
    lsp.open(&target, "\n# live surface moved\nhelper(x) = x + 1\n");
    let result = lsp.await_definition(&main, 1, 2);
    assert_eq!(result["uri"], uri(&target));
    assert_eq!(result["range"]["start"]["line"], 2);
    lsp.finish();
}

#[test]
fn configured_sibling_uses_previous_load_in_the_same_module() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    write(
        &root,
        "fatou.toml",
        "[project]\nentry-points = [\"main.jl\"]\n",
    );
    write(
        &root,
        "main.jl",
        "module ScriptHost\ninclude(\"a.jl\")\ninclude(\"b.jl\")\nend\n",
    );
    let expected = write(&root, "a.jl", "helper(x) = x\n");
    let caller = write(&root, "b.jl", "helper(1)\n");
    let mut lsp = Session::start(&root);
    lsp.open(&caller, "helper(1)\n");
    let result = lsp.await_definition(&caller, 0, 2);
    assert_eq!(result["uri"], uri(&expected));
    lsp.finish();
}

#[test]
fn loose_fallback_rejects_unproven_include_and_out_of_order_definition() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    write(&root, "helper.jl", "helper(x) = x\n");
    let mut lsp = Session::start(&root);
    for (i, (text, line)) in [
        ("helper(1)\ninclude(\"helper.jl\")\n", 0),
        (
            "include(x) = nothing\ninclude(\"helper.jl\")\nhelper(1)\n",
            2,
        ),
        ("if false\ninclude(\"helper.jl\")\nend\nhelper(1)\n", 3),
        ("path=\"helper.jl\"\ninclude(path)\nhelper(1)\n", 2),
        (
            "module OtherHost\ninclude(\"helper.jl\")\nend\nhelper(1)\n",
            3,
        ),
        (
            "function side()\ninclude(\"helper.jl\")\nend\nhelper(1)\n",
            3,
        ),
        ("quote\ninclude(\"helper.jl\")\nend\nhelper(1)\n", 3),
    ]
    .into_iter()
    .enumerate()
    {
        let caller = write(&root, &format!("caller{i}.jl"), text);
        lsp.open(&caller, text);
        assert_eq!(lsp.definition(&caller, line, 2), Value::Null, "{text}");
    }
    lsp.finish();
}

#[test]
fn script_can_follow_live_include_to_new_unsaved_file() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    let caller = write(&root, "main.jl", "helper(1)\n");
    let target = root.join("new.jl");
    let mut lsp = Session::start(&root);
    lsp.open(&caller, "include(\"new.jl\")\nhelper(1)\n");
    lsp.open(&target, "\nhelper(x) = x\n");
    let result = lsp.await_definition(&caller, 1, 2);
    assert_eq!(result["uri"], uri(&target));
    assert_eq!(result["range"]["start"]["line"], 1);
    assert!(!target.exists());
    lsp.finish();
}

#[test]
fn earlier_included_const_closure_only_blocks_later_same_module_edges() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    let helper = write(&root, "helper.jl", "helper(x) = x\n");
    write(&root, "shadow.jl", "const include = _ -> nothing\n");
    let mut lsp = Session::start(&root);
    for (i, (text, line, jumps)) in [
        ("module M\ninclude(\"shadow.jl\")\ninclude(\"helper.jl\")\nhelper(1)\nend\n",3,false),
        ("module M\ninclude(\"helper.jl\")\ninclude(\"shadow.jl\")\nhelper(1)\nend\n",3,true),
        ("module A\ninclude(\"shadow.jl\")\nend\nmodule B\ninclude(\"helper.jl\")\nhelper(1)\nend\n",5,true),
    ].into_iter().enumerate() {
        let caller = write(&root, &format!("probe{i}.jl"), text);
        lsp.open(&caller, text);
        let definition = lsp.definition(&caller, line, 2);
        if jumps { assert_eq!(definition["uri"], uri(&helper)); }
        else { assert_eq!(definition, Value::Null); }
    }
    lsp.finish();
}
