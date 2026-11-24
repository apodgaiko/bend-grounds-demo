"""Leak markers in a Python child's captured stderr (shared capture-boundary helper).

CPython prints some failures without changing the exit code: an exception in a
destructor ("Exception ignored ..."), an uncaught thread exception ("Exception in
thread ...", "Exception in threading.excepthook:") and, under the `default`
warnings action, a ResourceWarning as "file:N: ResourceWarning: ...". Under
`error::ResourceWarning` a warning raised outside a destructor is an uncaught
exception instead: rc 1 and a traceback whose last line is "ResourceWarning: ...";
a caller expecting some non-zero rc would pass it without this marker. A caller
that captures a child's stderr scans it with problems() after EVERY run, whatever
the exit code (expected error exits included), and fails on any match:

    sys.path.insert(0, os.path.join(ROOT, 'scripts'))   # project scripts/ import convention
    import child_stderr
    hits = child_stderr.problems(p.stderr)
    if hits:
        raise AssertionError('leak marker(s) in child stderr:\n' + '\n'.join(hits))

problems(stderr: str) -> list[str]: the matching lines, in order (empty = clean).
Stdlib only, no side effects on import.
"""
import re

# Match interpreter diagnostics that can otherwise hide behind a successful exit.
LEAK_RE = re.compile(r'^Exception (?:ignored|in thread(?:ing\.excepthook)?)\b', re.M)
# warnings.formatwarning under the `default` action: "<file>:<line>: ResourceWarning: <msg>"
WARN_RE = re.compile(r'^\S.*:\d+: ResourceWarning: ', re.M)
# Last line of a traceback for a raised ResourceWarning (also follows "Exception ignored ...").
RAISED_RE = re.compile(r'^ResourceWarning: ', re.M)


def problems(stderr):
    """Return the leak-marker lines of a child's stderr ([] if none)."""
    if not stderr:
        return []
    return [line for line in stderr.splitlines()
            if LEAK_RE.match(line) or WARN_RE.match(line) or RAISED_RE.match(line)]
