//! Full stdio coverage of same-file auto-import completion edits.

use std::fs;
use std::io::{BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration, Instant};

use fatou::text::{LineIndex, PositionEncoding};
use lsp_server::{ErrorCode, Message};
use lsp_types::{Position, TextEdit};
use serde_json::{Value, json};

const TOOLS: &str = "aaaaaaaa-bbbb-cccc-dddd-eeeeeeeeeeee";
const TOOLS2: &str = "aaaaaaaa-bbbb-cccc-dddd-ffffffffffff";

struct Session {
    child: Child,
    input: ChildStdin,
    messages: Receiver<Message>,
    next: i32,
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl Session {
    fn start(root: &Path) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_fatou"))
            .args(["lsp", "--no-config"])
            .current_dir(root)
            .env("JULIA_PROJECT", "@.")
            .env("JULIA_DEPOT_PATH", root.join("depot"))
            .env_remove("JULIA_BINDIR")
            .env("XDG_CACHE_HOME", root.join("cache"))
            .env("LOCALAPPDATA", root.join("cache"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("start Fatou");
        let input = child.stdin.take().unwrap();
        let mut stdout = BufReader::new(child.stdout.take().unwrap());
        let (sender, messages) = mpsc::channel();
        std::thread::spawn(move || {
            while let Ok(Some(message)) = Message::read(&mut stdout) {
                if sender.send(message).is_err() {
                    break;
                }
            }
        });
        let mut session = Self {
            child,
            input,
            messages,
            next: 0,
        };
        session.request(
            "initialize",
            json!({"processId":null,"rootUri":uri(root),"capabilities":{}}),
        );
        session.notify("initialized", json!({}));
        session
    }

    fn send(&mut self, value: Value) {
        serde_json::from_value::<Message>(value)
            .unwrap()
            .write(&mut self.input)
            .unwrap();
        self.input.flush().unwrap();
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(json!({"jsonrpc":"2.0","method":method,"params":params}));
    }

    fn request(&mut self, method: &str, params: Value) -> Value {
        self.next += 1;
        self.send(json!({"jsonrpc":"2.0","id":self.next,"method":method,"params":params}));
        let until = Instant::now() + Duration::from_secs(10);
        loop {
            let message = self
                .messages
                .recv_timeout(until.saturating_duration_since(Instant::now()))
                .unwrap_or_else(|error| panic!("{method}: {error}"));
            if let Message::Response(response) = message
                && response.id == self.next.into()
            {
                return match response.response_result {
                    Err(error)
                        if method == "textDocument/completion"
                            && error.code == ErrorCode::ContentModified as i32 =>
                    {
                        Value::Null
                    }
                    result => result.expect("successful LSP response"),
                };
            }
        }
    }

    fn open(&mut self, file: &Path, text: &str) {
        self.notify(
            "textDocument/didOpen",
            json!({"textDocument":{"uri":uri(file),"languageId":"julia","version":1,"text":text}}),
        );
    }

    fn completion(&mut self, file: &Path, position: Position) -> Vec<Value> {
        let result = self.request(
            "textDocument/completion",
            json!({"textDocument":{"uri":uri(file)},"position":position}),
        );
        result
            .as_array()
            .or_else(|| result["items"].as_array())
            .cloned()
            .unwrap_or_default()
    }

    fn await_completion(
        &mut self,
        file: &Path,
        position: Position,
        predicate: impl Fn(&[Value]) -> bool,
    ) -> Vec<Value> {
        let until = Instant::now() + Duration::from_secs(7);
        loop {
            let result = self.completion(file, position);
            if predicate(&result) {
                return result;
            }
            assert!(
                Instant::now() < until,
                "completion did not become ready ({} items, import candidates {:?})",
                result.len(),
                result
                    .iter()
                    .filter(|item| item["additionalTextEdits"].is_array())
                    .map(|item| &item["label"])
                    .collect::<Vec<_>>()
            );
            std::thread::sleep(Duration::from_millis(30));
        }
    }

    fn finish(mut self) {
        assert_eq!(self.request("shutdown", Value::Null), Value::Null);
        self.notify("exit", Value::Null);
        let until = Instant::now() + Duration::from_secs(5);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(status.success(), "{status}");
                break;
            }
            assert!(Instant::now() < until, "Fatou did not shut down");
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}

fn uri(path: &Path) -> String {
    let path = path.to_str().unwrap().replace('\\', "/");
    let path = path.strip_prefix("//?/").unwrap_or(&path);
    let slash = if path.starts_with('/') { "" } else { "/" };
    let mut encoded = String::new();
    for byte in path.bytes() {
        if byte.is_ascii_alphanumeric() || b"/:-_.~".contains(&byte) {
            encoded.push(char::from(byte));
        } else {
            use std::fmt::Write;
            write!(encoded, "%{byte:02X}").unwrap();
        }
    }
    format!("file://{slash}{encoded}")
}

fn write(root: &Path, relative: &str, text: &str) -> PathBuf {
    let path = root.join(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, text).unwrap();
    path
}

fn dependencies(root: &Path, package: bool, ambiguous: bool) {
    let header = if package {
        "name = \"Tester\"\nuuid = \"eeeeeeee-bbbb-cccc-dddd-eeeeeeeeeeee\"\n"
    } else {
        ""
    };
    let second = if ambiguous {
        format!("Tools2 = \"{TOOLS2}\"\n")
    } else {
        String::new()
    };
    write(
        root,
        "Project.toml",
        &format!("{header}[deps]\nTools = \"{TOOLS}\"\n{second}"),
    );
    let second_pin = if ambiguous {
        format!("[[deps.Tools2]]\nuuid = \"{TOOLS2}\"\npath = \"Tools2\"\n")
    } else {
        String::new()
    };
    write(
        root,
        "Manifest.toml",
        &format!(
            "manifest_format = \"2.0\"\n[[deps.Tools]]\nuuid = \"{TOOLS}\"\npath = \"Tools\"\n{second_pin}"
        ),
    );
    write(
        root,
        "Tools/src/Tools.jl",
        "module Tools\nexport calculate, calculator, calc_undefined\ncalculate() = 2\nstruct calculator end\nend\n",
    );
    if ambiguous {
        write(
            root,
            "Tools2/src/Tools2.jl",
            "module Tools2\nexport calculate\ncalculate() = 3\nend\n",
        );
    }
}

fn auto_import<'a>(items: &'a [Value], label: &str) -> Option<&'a Value> {
    items
        .iter()
        .find(|item| item["label"] == label && item["additionalTextEdits"].is_array())
}

fn assert_edit(item: &Value, source: &str, anchor: Position, target: Position, eol: &str) {
    assert_eq!(item["detail"], "Auto-import from Tools");
    let primary: TextEdit = serde_json::from_value(item["textEdit"].clone()).unwrap();
    let extra: Vec<TextEdit> = serde_json::from_value(item["additionalTextEdits"].clone()).unwrap();
    let [import] = extra.as_slice() else {
        panic!("expected one edit, got {extra:?}");
    };
    assert_eq!(primary.range.start, target);
    assert_eq!(
        primary.range.end,
        Position::new(target.line, target.character + 4)
    );
    assert_eq!(primary.new_text, "calculate");
    assert_eq!(import.range.start, anchor);
    assert_eq!(import.range.end, anchor);
    assert_eq!(import.new_text, format!("using Tools: calculate{eol}"));
    let lines = LineIndex::new(source);
    let bytes = |position| lines.position_to_byte(position, PositionEncoding::Utf16);
    let at = bytes(anchor);
    let start = bytes(primary.range.start);
    let end = bytes(primary.range.end);
    assert!(at < start);
    let mut applied = source.to_owned();
    applied.replace_range(start..end, &primary.new_text);
    applied.insert_str(at, &import.new_text);
    assert!(
        fatou::parser::parse(&applied).diagnostics.is_empty(),
        "{applied}"
    );
    assert_eq!(
        applied
            .lines()
            .filter(|line| line.starts_with("using "))
            .count(),
        1
    );
}

#[test]
fn auto_import_real_stdio_named_and_unnamed_projects() {
    for package in [false, true] {
        let tmp = tempfile::tempdir().unwrap();
        let root = std::path::absolute(tmp.path()).unwrap();
        dependencies(&root, package, false);
        let (file, sibling, source, anchor, target, eol) = if package {
            write(
                &root,
                "src/Tester.jl",
                "module Tester\ninclude(\"sibling.jl\")\ninclude(\"lib/use.jl\")\nend\n",
            );
            let sibling = write(&root, "src/sibling.jl", "sentinel() = 1\n");
            let source = "# member comment\nsentinel()\nf() = (\"🚀\"; calc())\n";
            (
                write(&root, "src/lib/use.jl", source),
                Some(sibling),
                source,
                Position::new(1, 0),
                Position::new(2, 13),
                "\n",
            )
        } else {
            let source = "#!/usr/bin/julia\r\n# loose script\r\nn = 1\r\nf() = (\"🚀\"; calc())\r\n";
            (
                write(&root, "run.jl", source),
                None,
                source,
                Position::new(2, 0),
                Position::new(3, 13),
                "\r\n",
            )
        };
        let mut session = Session::start(&root);
        session.open(&file, source);
        let cursor = Position::new(target.line, target.character + 4);
        let items = session.await_completion(&file, cursor, |items| {
            auto_import(items, "calculate").is_some()
        });
        assert_edit(
            auto_import(&items, "calculate").unwrap(),
            source,
            anchor,
            target,
            eol,
        );
        assert!(auto_import(&items, "calc_undefined").is_none());
        if let Some(sibling) = sibling {
            // The live sibling introduces a conflicting global without saving to disk.
            session.open(&sibling, "sentinel() = 1\ncalculate() = 0\n");
            let items = session.await_completion(&file, cursor, |items| {
                auto_import(items, "calculate").is_none()
                    && auto_import(items, "calculator").is_some()
            });
            assert!(auto_import(&items, "calculate").is_none());
            assert_eq!(fs::read_to_string(sibling).unwrap(), "sentinel() = 1\n");
        }
        session.finish();
    }
}

#[test]
fn auto_import_real_stdio_omits_ambiguous_and_missing_exports() {
    let tmp = tempfile::tempdir().unwrap();
    let root = std::path::absolute(tmp.path()).unwrap();
    dependencies(&root, false, true);
    let source = "start = 1\nf() = calc()\n";
    let file = write(&root, "run.jl", source);
    let mut session = Session::start(&root);
    session.open(&file, source);
    let items = session.await_completion(&file, Position::new(1, 10), |items| {
        auto_import(items, "calculator").is_some()
    });
    assert!(auto_import(&items, "calculate").is_none());
    assert!(auto_import(&items, "calc_undefined").is_none());
    session.finish();
}
