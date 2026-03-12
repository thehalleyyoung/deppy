"""Harder VALUE_ERROR: int/float parsing and list.remove in complex patterns."""

BUG_TYPE = "VALUE_ERROR"
BUG_DESC = "Value error in complex parsing and removal patterns"

EXAMPLES = [
    (
        "parse_csv_field",
        # buggy: int() on field that may not be numeric
        '''\
def parse_ages(csv_line):
    fields = csv_line.split(",")
    ages = []
    for f in fields:
        ages.append(int(f))
    return ages
''',
        # safe: try/except around parsing
        '''\
def parse_ages(csv_line):
    fields = csv_line.split(",")
    ages = []
    for f in fields:
        try:
            ages.append(int(f))
        except ValueError:
            pass
    return ages
''',
        "int() on CSV field that may contain non-numeric data",
    ),
    (
        "remove_from_queue",
        # buggy: remove item that may not be in list
        '''\
def cancel_job(queue, job_id):
    queue.remove(job_id)
    return queue
''',
        # safe: membership check before remove
        '''\
def cancel_job(queue, job_id):
    if job_id in queue:
        queue.remove(job_id)
    return queue
''',
        "list.remove() on item that may not exist",
    ),
    (
        "parse_float_input",
        # buggy: float() on user input
        '''\
def read_measurement(raw):
    cleaned = raw.strip()
    value = float(cleaned)
    return value
''',
        # safe: try/except
        '''\
def read_measurement(raw):
    cleaned = raw.strip()
    try:
        value = float(cleaned)
    except ValueError:
        value = 0.0
    return value
''',
        "float() on user-provided string that may not be numeric",
    ),
]
