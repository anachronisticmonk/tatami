#!/usr/bin/env python3
"""Dev server for the playground.

Serves the playground and forwards each translation to the Lean binary, so the
page shows what the real implementation produces rather than its own
JavaScript fallback.

    lake build && python3 dev/serve.py    then open http://localhost:8420

Two pages, the same engine behind both: the React one at /, and the original
at /classic. TATAMI_PLAYGROUND_PORT moves it off 8420.

Everything a checkout gets for free -- the binary under .lake, the pages under
web/, loopback -- an image has to be told, because an image has no checkout to
infer them from. So each of those is a default rather than a constant:

    TATAMI_PLAYGROUND_ADDR   bind address        (default 127.0.0.1)
    TATAMI_PLAYGROUND_PORT   bind port           (default 8420)
    TATAMI_WEB               directory of pages  (default <root>/web)
    TATAMI_BINARY            the generator       (default <root>/.lake/build/bin/tatami)

TATAMI_WEB is spelled the same as bin/serve.ml's, so one variable points both
servers at the same pages. The address stays loopback unless asked: a server
should not appear on the network because someone started it -- but published
ports forward to the container's external interface, so inside a container
127.0.0.1 is reachable only from inside that container, which looks exactly
like a working server and a broken port mapping.
"""

import http.server
import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent


def _path(env, default):
    """Env override for a path, taken as written (so a relative TATAMI_WEB
    means the same thing here as it does to bin/serve.exe: relative to cwd)."""
    value = os.environ.get(env)
    return pathlib.Path(value) if value else default


WEB = _path("TATAMI_WEB", ROOT / "web")
BINARY = _path("TATAMI_BINARY", ROOT / ".lake" / "build" / "bin" / "tatami")
PAGE = _path("TATAMI_PLAYGROUND_PAGE", WEB / "playground-react.html")
CLASSIC = _path("TATAMI_PLAYGROUND_CLASSIC", WEB / "playground.html")
ADDR = os.environ.get("TATAMI_PLAYGROUND_ADDR", "127.0.0.1")
PORT = int(os.environ.get("TATAMI_PLAYGROUND_PORT", 8420))


class Handler(http.server.BaseHTTPRequestHandler):
    def _send(self, body, content_type):
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = self.path.split("?")[0]
        if path in ("/", "/index.html"):
            self._send(PAGE.read_bytes(), "text/html; charset=utf-8")
        elif path == "/classic":
            self._send(CLASSIC.read_bytes(), "text/html; charset=utf-8")
        else:
            self.send_error(404)

    def do_POST(self):
        if self.path != "/translate":
            return self.send_error(404)
        length = int(self.headers.get("Content-Length") or 0)
        body = self.rfile.read(length)

        # The page sends {"input": <json text>, "config": {...}}. The config is
        # written to a temp file because that is the interface the binary has:
        # a config is a file, exactly as a user would keep one.
        config_path = None
        try:
            envelope = json.loads(body)
            payload = envelope.get("input", "").encode()
            config = envelope.get("config") or {}
        except (ValueError, AttributeError):
            payload, config = body, {}

        argv = [str(BINARY), "--json"]
        if config:
            fd, config_path = tempfile.mkstemp(suffix=".json")
            with os.fdopen(fd, "w") as f:
                json.dump(config, f)
            argv += ["--config", config_path]

        try:
            run = subprocess.run(
                argv, input=payload, capture_output=True, timeout=15)
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
        finally:
            if config_path:
                os.unlink(config_path)
        self._send(out, "application/json")

    def log_message(self, *args):
        pass


if __name__ == "__main__":
    # flush=True throughout: under a container runtime stdout is a pipe, and a
    # block-buffered pipe holds these lines until the process ends, which is
    # exactly when nobody needs them any more.
    if not BINARY.exists():
        print(f"warning: {BINARY} does not exist. Run `lake build` first.",
              file=sys.stderr, flush=True)
    host = "localhost" if ADDR in ("127.0.0.1", "0.0.0.0", "::", "") else ADDR
    print(f"tatami playground on http://{host}:{PORT}  (serving {PAGE.name} through {BINARY.name})",
          flush=True)
    print(f"the original page is at http://{host}:{PORT}/classic", flush=True)
    print(f"  bound to {ADDR}:{PORT}", flush=True)
    http.server.ThreadingHTTPServer((ADDR, PORT), Handler).serve_forever()
