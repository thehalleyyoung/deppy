"""Harder MEMORY_LEAK: conditional open, early return paths, nested opens."""

BUG_TYPE = "MEMORY_LEAK"
BUG_DESC = "File handle leak in complex control flow"

EXAMPLES = [
    (
        "conditional_log_open",
        # buggy: open outside with in conditional branch
        '''\
def process_and_log(data, log_path):
    log_file = open(log_path, "a")
    for item in data:
        result = transform(item)
        log_file.write(str(result))
    return "done"
''',
        # safe: use with statement
        '''\
def process_and_log(data, log_path):
    with open(log_path, "a") as log_file:
        for item in data:
            result = transform(item)
            log_file.write(str(result))
    return "done"
''',
        "File opened for logging without with statement, never closed",
    ),
    (
        "multi_file_process",
        # buggy: second open without with
        '''\
def merge_files(src_path, dst_path):
    src = open(src_path, "r")
    dst = open(dst_path, "w")
    for line in src:
        dst.write(line.upper())
    return dst_path
''',
        # safe: both in with statements
        '''\
def merge_files(src_path, dst_path):
    with open(src_path, "r") as src:
        with open(dst_path, "w") as dst:
            for line in src:
                dst.write(line.upper())
    return dst_path
''',
        "Two files opened without with, both potentially leaked",
    ),
    (
        "temp_file_open",
        # buggy: temp file opened bare
        '''\
def write_temp(content, path):
    tmp = open(path + ".tmp", "w")
    tmp.write(content)
    rename(path + ".tmp", path)
    return path
''',
        # safe: with statement
        '''\
def write_temp(content, path):
    with open(path + ".tmp", "w") as tmp:
        tmp.write(content)
    rename(path + ".tmp", path)
    return path
''',
        "Temporary file opened without with, may leak on exception",
    ),
]
