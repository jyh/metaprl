#!/usr/bin/env python3
"""mpdrive: drive one `mp -cli` over a pipe, one command per step (O95, the MetaPRL arm).

usage: mpdrive.py ROOT SCRIPT [--step-timeout S] [--start-timeout S]
  ROOT    a metaprl tree (editor/ml/mp is started there)
  SCRIPT  a file of MetaPRL shell commands, one per line, each ending in ';;'
          ('#' lines and blank lines are skipped)

Each step is delimited by an integer sentinel (the shell echoes `# N : int` in -cli).
Prints, per step: `=== STEP k [ok|ERR|TIMEOUT|EOF] <secs>s :: <command>` then the step's output;
after a refine, `=== CHILDREN k: <label> ...` (the rule box's direct children, `-` = no label).
Ends with `=== END steps=<n> ok=<n> rc=<rc>` and the .cmoz files the session wrote.
LIMITS: a TIMEOUT kills the mp process (by its own pid); later steps are not run.
The shell is NOT an OCaml toplevel (print_endline is unbound); only integer sentinels delimit.
-cli writes <module>.cmoz at exit and later sessions load it before the stored proof:
the END line lists every .cmoz written so the caller can remove or keep it on purpose.
"""
import os, sys, time, select, subprocess, glob, re

VALUE_RE = re.compile(r'(?m)^(# )?.*\S : [A-Za-z_][A-Za-z_0-9 .]*$')

def wrap(c, width=200):
    """Split a command into lines of at most `width` characters, at spaces."""
    out, cur = [], ''
    for w in c.split(' '):
        if cur and len(cur) + 1 + len(w) > width:
            out.append(cur); cur = w
        else:
            cur = w if not cur else cur + ' ' + w
    if cur:
        out.append(cur)
    return out

def children(txt):
    """The direct children of a refine's rule box, in order, by label: a label
    line directly under a child header `N. [` at column 0, after the BY line.
    An empty label (........) is printed as `-`. Nested nodes under a child
    (a stored subtree still attached to it) are not direct children."""
    import re
    lines = re.sub(r'\x1b\[[0-9;]*m', '', txt).split('\n')
    out, by, prev = [], False, ''
    for l in lines:
        if l.startswith('BY '):
            by = True
        elif by and prev and re.match(r'^[0-9]+\. \[', prev):
            m = re.match(r'^   \.\.\.\.([a-z ]*)\.\.\.\.$', l)
            if m:
                out.append(m.group(1) or '-')
        prev = l
    return out

def main():
    a = sys.argv[1:]
    if len(a) < 2:
        print(__doc__); return 2
    root, script = a[0], a[1]
    step_to = float(a[a.index('--step-timeout') + 1]) if '--step-timeout' in a else 60.0
    start_to = float(a[a.index('--start-timeout') + 1]) if '--start-timeout' in a else 60.0
    cmds = [l.rstrip('\n') for l in open(script) if l.strip() and not l.lstrip().startswith('#')]
    t_start = time.time()
    mp = os.path.join(root, 'editor', 'ml', 'mp')
    p = subprocess.Popen([mp, '-cli'], cwd=root, stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
    buf = b''
    def until(tag, timeout):
        nonlocal buf
        t0 = time.time()
        while True:
            i = buf.find(tag)
            if i >= 0:
                j = buf.find(b'\n', i)
                j = len(buf) if j < 0 else j + 1
                out, buf = buf[:i], buf[j:]
                return 'ok', out, time.time() - t0
            left = timeout - (time.time() - t0)
            if left <= 0:
                return 'TIMEOUT', buf, time.time() - t0
            r, _, _ = select.select([p.stdout], [], [], min(left, 1.0))
            if r:
                d = os.read(p.stdout.fileno(), 65536)
                if not d:
                    return 'EOF', buf, time.time() - t0
                buf += d
    def send(s):
        p.stdin.write(s.encode() + b'\n'); p.stdin.flush()
    # start-up: discard everything before the first sentinel
    send('900000;;')
    st, _, dt = until(b'# 900000 : int', start_to)
    print(f'=== START [{st}] {dt:.1f}s', flush=True)
    ok = n = 0
    nerr = [0]
    rc = 0
    if st != 'ok':
        rc = 3
    else:
        for k, c in enumerate(cmds, 1):
            n += 1
            sent = 900000 + k
            # Until libmojave #117 (merged 2026-11-01) mp's input was read by a 1,023-byte
            # fgets and a longer line broke at character 1023 (D2). A clone built against an
            # older libmojave still has that limit: steps/d2-long.mp (1,204 chars) tells.
            # The bound below is a sanity limit only.
            if c.lstrip().startswith(('export', 'save')) and nerr[0] > 0:
                print(f'=== STEP {k} [REFUSED] 0.00s :: {c} (an earlier step erred: an archive is never written from a failed session)', flush=True)
                continue
            if len(c) > 100000:
                print(f'=== STEP {k} [REFUSED] 0.00s :: {c[:120]}... ({len(c)} chars > 100000)', flush=True)
                rc = 5; break
            send(c); send(f'{sent};;')
            st, out, dt = until(f'# {sent} : int'.encode(), step_to)
            txt = out.decode('utf-8', 'replace')
            # A phrase that succeeds ends by printing its value (`v : type`); a failed one prints only
            # the exception. The needles alone read a failed cd (`Invalid Argument`, `wrong magic number`)
            # as ok, and an export after it wrote the PREVIOUS module's archive (D3, runs-p2-07 step 18).
            if st == 'ok' and (not VALUE_RE.search(txt) or
                               any(m in txt for m in ('Failure', 'error', 'Error', 'Exception', 'not found', 'undefined'))):
                st_shown = 'ERR'; nerr[0] += 1
            else:
                st_shown = st
            print(f'=== STEP {k} [{st_shown}] {dt:.2f}s :: {c}', flush=True)
            sys.stdout.write(out.decode('utf-8', 'replace')); sys.stdout.flush()
            if c.lstrip().startswith('refine'):
                print(f'=== CHILDREN {k}: ' + ' '.join(children(txt)), flush=True)
            if st != 'ok':
                rc = 4; break
            ok += 1
    if p.poll() is None:
        if rc:
            p.kill()
        else:
            try:
                p.stdin.close(); p.wait(timeout=30)
            except Exception:
                p.kill()
    p.wait()
    cm = [f for f in glob.glob(os.path.join(root, 'theories', '**', '*.cmoz'), recursive=True)
          if os.path.getmtime(f) >= t_start]
    print(f'=== END steps={n} ok={ok} err={nerr[0]} rc={rc} cmoz-written={len(cm)}')
    for f in cm:
        print(f'    CMOZ {os.path.relpath(f, root)}')
    return rc

if __name__ == '__main__':
    sys.exit(main())
