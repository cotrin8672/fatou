"""Run the prototype over stdio with an actual bridge demo's exported JSON."""
from pathlib import Path
import copy
import itertools
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FILE = HERE / "fixture.jl"
URI = FILE.as_uri()
binary = str(Path(sys.argv[1]).resolve())
source = FILE.read_bytes().decode("utf-8")
report = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
assert report["source"] == source
assert Path(report["sourcePath"]).resolve() == FILE
assert len(report["hints"]) == 5
extra_reports = [json.loads(Path(x).read_text(encoding="utf-8")) for x in sys.argv[3:]]
assert len(extra_reports) in (0, 3)
assert all(x["sourcePath"] == report["sourcePath"] and x["source"] == source for x in extra_reports)


class Wire:
    def __init__(self, cwd):
        self.p = subprocess.Popen(
            [binary, "--no-config", "lsp"],
            cwd=cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )
        self.ids = itertools.count(1)
        self.refreshes = 0

    def send(self, **params):
        content = json.dumps({"jsonrpc": "2.0", **params}).encode()
        self.p.stdin.write(f"Content-Length: {len(content)}\r\n\r\n".encode() + content)
        self.p.stdin.flush()

    def request(self, method, params):
        call = next(self.ids)
        self.send(id=call, method=method, params=params)
        while True:
            headers = {}
            while True:
                row = self.p.stdout.readline()
                if not row:
                    raise RuntimeError("Fatou quit before replying")
                if not row.strip():
                    break
                k, v = row.decode().split(":", 1)
                headers[k.lower()] = v.strip()
            reply = json.loads(self.p.stdout.read(int(headers["content-length"])))
            if reply.get("method") == "workspace/inlayHint/refresh":
                self.refreshes += 1
            if "method" in reply and "id" in reply:
                self.send(id=reply["id"], result=[])
            if "method" not in reply and reply.get("id") == call:
                return reply


def run(encoding):
    c = Wire(HERE)
    p = c.p
    try:
        init = c.request(
            "initialize",
            {
                "rootUri": None,
                "capabilities": {
                    "workspace": {"inlayHint": {"refreshSupport": True}},
                    "general": {"positionEncodings": [encoding]},
                },
            },
        )["result"]
        assert init["capabilities"]["positionEncoding"] == encoding
        c.send(method="initialized", params={})

        def opened(ver=1, uri=URI):
            c.send(
                method="textDocument/didOpen",
                params={
                    "textDocument": {
                        "uri": uri,
                        "languageId": "julia",
                        "version": ver,
                        "text": source,
                    },
                },
            )

        def menu(first=0, last=99):
            return c.request(
                "textDocument/inlayHint",
                {
                    "textDocument": {"uri": URI},
                    "range": {
                        "start": {"line": first, "character": 0},
                        "end": {"line": last, "character": 0},
                    },
                },
            )["result"]

        def target(uri=URI):
            return c.request("fatou/compilerHintsTarget", {"uri": uri})["result"]

        def import_(ticket, snapshot=report, uri=URI):
            return c.request(
                "fatou/compilerHintsImport", {"uri": uri, **ticket, "snapshot": snapshot}
            )

        opened()
        assert menu() == []
        assert "error" in c.request("fatou/compilerHintsTarget", {"uri": "untitled:doc"})
        ticket = target()
        assert import_(ticket)["result"] == {"imported": 5}
        assert "error" in import_(ticket), "one-use ticket must not replay"
        result = menu()
        expected = [
            (10, 18, "::Tuple{Int64, Float64, Int64, Float64}"),
            (11, 5, "::Int64"),
            (12, 6 if encoding == "utf-8" else 5, "::Float64"),
            (13, 5, "::Int64"),
            (14, 5, "::Float64"),
        ]
        assert [(h["position"]["line"], h["position"]["character"], h["label"]) for h in result] == expected, result
        assert len(menu(12, 13)) == 1 and menu(40, 50) == []
        assert all(h["kind"] == 1 and "textEdits" not in h and "explicit argument types" in h["tooltip"] for h in result)
        assert c.refreshes >= 1
        wrong_file = HERE / "identical_but_wrong_path.jl"
        opened(uri=wrong_file.as_uri())
        assert "error" in import_(target(wrong_file.as_uri()), uri=wrong_file.as_uri())
        assert len(menu()) == 5
        wrong_src = copy.deepcopy(report)
        wrong_src["source"] += "# unsaved mismatch\n"
        assert "error" in import_(target(), wrong_src)
        split = copy.deepcopy(report)
        split["hints"][1]["endByte"] -= 1
        assert "error" in import_(target(), split), "reject offset inside a UTF-8 character"
        stale = target()
        c.send(
            method="textDocument/didChange",
            params={"textDocument": {"uri": URI, "version": 2}, "contentChanges": [{"text": source + "# stale\n"}]},
        )
        assert menu() == []
        assert "error" in import_(stale), "edit invalidates pending ticket"
        assert "error" in import_(target()), "new ticket does not excuse old source"
        c.send(method="textDocument/didClose", params={"textDocument": {"uri": URI}})
        opened(ver=1) # same version and bytes, but the old ticket is still invalid.
        assert "error" in import_(ticket)
        assert import_(target())["result"] == {"imported": 5}
        assert len(menu()) == 5
        c.request("fatou/compilerHintsClear", {})
        assert menu() == []
        assert c.refreshes >= 3
        if extra_reports:
            expected_extra = [
                (extra_reports[0], [(17, 39, "::Any"), (18, 8, "::Any")], "did not narrow"),
                (extra_reports[1], [(22, 27, "::Union{}")], "no normal return"),
                (extra_reports[2], [(26, 31, "::Union{Nothing, Int64}")], None),
            ]
            for snapshot, labels, phrase in expected_extra:
                assert import_(target(), snapshot)["result"] == {"imported": len(labels)}
                found = menu()
                assert [(h["position"]["line"], h["position"]["character"], h["label"]) for h in found] == labels, found
                if phrase:
                    assert all(phrase in h["tooltip"] for h in found), found
                else:
                    assert all("did not narrow" not in h["tooltip"] and "no normal return" not in h["tooltip"] for h in found), found
            c.request("fatou/compilerHintsClear", {})
            assert menu() == []
        c.request("shutdown", None)
        c.send(method="exit")
        p.wait(timeout=3)
        print(json.dumps({"encoding": encoding, "verified": len(result), "extra_inferred": 4 if extra_reports else 0, "refreshes": c.refreshes}))
    finally:
        if p.poll() is None:
            p.kill()
            p.wait()


for enc in ("utf-8", "utf-16"):
    run(enc)
