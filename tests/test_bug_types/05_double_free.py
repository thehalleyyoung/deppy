"""DOUBLE_FREE: Double close/free — resource lifetime obstruction.

Required section: lifetime(resource) = OPEN at close site.
"""

BUG_TYPE = "DOUBLE_CLOSE"

BUGGY_A = r"""
def process_file(path):
    f = open(path)
    data = f.read()
    f.close()
    f.close()
    return data
"""

SAFE_A = r"""
def process_file(path):
    with open(path) as f:
        data = f.read()
    return data
"""

BUGGY_B = r"""
def copy_file(src, dst):
    f_in = open(src)
    f_out = open(dst, 'w')
    f_out.write(f_in.read())
    f_in.close()
    f_out.close()
    f_in.close()
    return True
"""

SAFE_B = r"""
def copy_file(src, dst):
    with open(src) as f_in:
        with open(dst, 'w') as f_out:
            f_out.write(f_in.read())
    return True
"""

BUGGY_C = r"""
def read_and_summarize(path):
    handle = open(path)
    lines = handle.readlines()
    handle.close()
    handle.close()
    return len(lines)
"""

SAFE_C = r"""
def read_and_summarize(path):
    with open(path) as handle:
        lines = handle.readlines()
    return len(lines)
"""

EXAMPLES = [
    ("double_close_file", BUGGY_A, SAFE_A, "File closed twice"),
    ("copy_double_close", BUGGY_B, SAFE_B, "f_in closed twice in copy"),
    ("read_double_close", BUGGY_C, SAFE_C, "handle closed twice"),
]

BUG_DESC = "Resource closed/freed twice — second close on already-closed resource."
