"""Run the terminal app in a pseudo-terminal, send keys, and collect screen snapshots.

Used by the headless smoke test; also handy by hand:

    python3 scripts/statement_checker/tests/ptydrive.py 80 24 'j j \\n' -- --reviewer Test
"""
import fcntl
import os
import pty
import select
import struct
import sys
import tempfile
import termios
import time
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[2] / "check_statements.py"


def run(keys, cols=80, rows=24, args=(), env=None, settle=0.25, timeout=60):
    """Start the app, wait until it draws, send each key (a string), snapshot after each one.

    Returns (exit status, list of snapshots, raw output bytes)."""
    snap = tempfile.NamedTemporaryFile(prefix="snap_", suffix=".txt", delete=False).name
    environ = dict(os.environ, TERM="xterm-256color", CHECK_STATEMENTS_SNAPSHOT=snap,
                   LANG=os.environ.get("LANG", "C.UTF-8") if "UTF-8" in os.environ.get("LANG", "") else "C.UTF-8",
                   ESCDELAY="25")
    environ.update(env or {})
    pid, fd = pty.fork()
    if pid == 0:  # child
        os.execvpe(sys.executable, [sys.executable, str(SCRIPT), *args], environ)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))
    out = bytearray()

    def pump(seconds):
        end = time.time() + seconds
        while time.time() < end:
            r, _, _ = select.select([fd], [], [], 0.05)
            if r:
                try:
                    data = os.read(fd, 65536)
                except OSError:
                    return False
                if not data:
                    return False
                out.extend(data)
        return True

    snaps = []

    def wait_snapshot(old):
        end = time.time() + timeout
        while time.time() < end:
            if not pump(0.1):
                return
            try:
                text = Path(snap).read_text(encoding="utf-8")
            except OSError:
                text = ""
            if text and text != old:
                pump(settle)
                return
        return

    wait_snapshot("")
    snaps.append(Path(snap).read_text(encoding="utf-8") if os.path.exists(snap) else "")
    for k in keys:
        os.write(fd, k.encode("utf-8"))
        pump(settle)
        try:
            snaps.append(Path(snap).read_text(encoding="utf-8"))
        except OSError:
            snaps.append("")
    # wait for the process to end
    end = time.time() + timeout
    status = None
    while time.time() < end:
        pump(0.1)
        p, st = os.waitpid(pid, os.WNOHANG)
        if p:
            status = os.waitstatus_to_exitcode(st)
            break
    if status is None:
        os.kill(pid, 9)
        os.waitpid(pid, 0)
    os.close(fd)
    os.unlink(snap)
    return status, snaps, bytes(out)


if __name__ == "__main__":
    cols, rows, keys = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    args = sys.argv[5:] if len(sys.argv) > 4 and sys.argv[4] == "--" else []
    seq = [k.encode().decode("unicode_escape") for k in keys.split(" ") if k]
    status, snaps, _ = run(seq, cols, rows, args)
    for k, s in enumerate(snaps):
        print(f"=== after {k} keys ===")
        print(s)
    print("exit", status)
