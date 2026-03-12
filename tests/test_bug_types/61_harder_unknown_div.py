"""Harder unknown module tests: bugs involving calls to unknown libraries."""

BUG_TYPE = "DIV_ZERO"
BUG_DESC = "Division by zero involving unknown module return values"

EXAMPLES = [
    (
        "unknown_lib_divisor",
        # buggy: unknown library returns value used as divisor
        '''\
import scipy.stats as stats
def normalized_score(values, target):
    result = stats.zscore(values)
    spread = result.std()
    return target / spread
''',
        # safe: guard divisor
        '''\
import scipy.stats as stats
def normalized_score(values, target):
    result = stats.zscore(values)
    spread = result.std()
    if spread == 0:
        return 0.0
    return target / spread
''',
        "Division by result from unknown library that may be zero",
    ),
    (
        "unknown_count_divisor",
        # buggy: count from unknown API used as divisor
        '''\
import db_client
def avg_response_time(session):
    total = db_client.sum_column(session, "response_ms")
    count = db_client.count_rows(session, "requests")
    return total / count
''',
        # safe: check count
        '''\
import db_client
def avg_response_time(session):
    total = db_client.sum_column(session, "response_ms")
    count = db_client.count_rows(session, "requests")
    if not count:
        return 0.0
    return total / count
''',
        "Division by count from unknown database client",
    ),
    (
        "unknown_metric_divisor",
        # buggy: metric from unknown monitoring lib as divisor
        '''\
import prometheus_client as prom
def error_rate(counter_name):
    errors = prom.get_metric(counter_name + "_errors")
    total = prom.get_metric(counter_name + "_total")
    return errors / total
''',
        # safe: guard total
        '''\
import prometheus_client as prom
def error_rate(counter_name):
    errors = prom.get_metric(counter_name + "_errors")
    total = prom.get_metric(counter_name + "_total")
    if total == 0:
        return 0.0
    return errors / total
''',
        "Division by metric from unknown monitoring library",
    ),
]
