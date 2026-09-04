#!/usr/bin/env python3
"""Dev server for the playground.

Serves web/playground.html and forwards each translation to the Lean binary,
so the page shows what the real implementation produces rather than its own
JavaScript fallback.

    lake build && python3 dev/serve.py    then open http://localhost:8420
"""

import http.server
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake" / "build" / "bin" / "tatami"
PAGE = ROOT / "web" / "playground.html"
PORT = 8420


class Handler(http.server.BaseHTTPRequestHandler):
    def _send(self, body, content_type):
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path.split("?")[0] in ("/", "/index.html"):
            self._send(PAGE.read_bytes(), "text/html; charset=utf-8")
        else:
            self.send_error(404)

    def do_POST(self):
        if self.path != "/translate":
            return self.send_error(404)
        length = int(self.headers.get("Content-Length") or 0)
        payload = self.rfile.read(length)
        try:
            run = subprocess.run(
                [str(BINARY), "--json"], input=payload,
                capture_output=True, timeout=15)
            out = run.stdout.strip()
            if not out:
                out = json.dumps({
                    "ok": False,
                    "error": run.stderr.decode("utf-8", "replace").strip()
                            or "the generator produced no output"
                }).encode()
        except FileNotFoundError:
            out = json.dumps({
                "ok": False,
                "error": "the generator is not built. Run `lake build` and reload."
            }).encode()
        except subprocess.TimeoutExpired:
            out = json.dumps({"ok": False, "error": "the generator timed out"}).encode()
        self._send(out, "application/json")

    def log_message(self, *args):
        pass


if __name__ == "__main__":
    if not BINARY.exists():
        print(f"warning: {BINARY} does not exist. Run `lake build` first.", file=sys.stderr)
    print(f"tatami playground on http://localhost:{PORT}  (serving {PAGE.name} through {BINARY.name})")
    http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
