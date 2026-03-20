#!/usr/bin/env python3
"""Large benchmark suite: 100 Python programs for bug detection.

60 programs WITH genuine bugs, 40 programs WITHOUT bugs (safe).
Covers all 22 bug types from deppy's taxonomy:
  DIV_ZERO, INDEX_OOB, KEY_ERROR, NULL_PTR, TYPE_CONFUSION, TYPE_ERROR,
  UNBOUND_VAR, VALUE_ERROR, USE_AFTER_FREE, MEMORY_LEAK, STACK_OVERFLOW,
  SQL_INJECTION, COMMAND_INJECTION, XSS, INTEGER_OVERFLOW, DOUBLE_FREE,
  RACE_CONDITION, DEADLOCK, INFINITE_LOOP, ASSERTION_FAILURE, FORMAT_STRING,
  TIMING_CHANNEL

Each entry: (name, source, expected_bugs, expected_fix_count)
"""

from __future__ import annotations

import textwrap
from typing import List, Tuple

BUG_PROGRAMS: List[Tuple[str, str, List[str], int]] = [

    # ======================================================================
    #  1-3: DIV_ZERO  (3 buggy)
    # ======================================================================
    ("div_zero_mean", textwrap.dedent("""\
        def mean(values):
            return sum(values) / len(values)
    """), ["DIV_ZERO"], 1),

    ("div_zero_weighted", textwrap.dedent("""\
        def weighted_avg(vals, weights):
            total_w = sum(weights)
            return sum(v * w for v, w in zip(vals, weights)) / total_w
    """), ["DIV_ZERO"], 1),

    ("div_zero_ratio_pair", textwrap.dedent("""\
        def ratio_pair(a, b, c):
            return a / b, a / c
    """), ["DIV_ZERO", "DIV_ZERO"], 2),

    # ======================================================================
    #  4-6: INDEX_OOB  (3 buggy)
    # ======================================================================
    ("index_oob_last", textwrap.dedent("""\
        def last(lst):
            return lst[len(lst)]
    """), ["INDEX_OOB"], 1),

    ("index_oob_sliding_window", textwrap.dedent("""\
        def sliding_avg(data, k):
            results = []
            for i in range(len(data)):
                window = [data[i + j] for j in range(k)]
                results.append(sum(window) / k)
            return results
    """), ["INDEX_OOB"], 1),

    ("index_oob_matrix", textwrap.dedent("""\
        def trace(matrix, n):
            total = 0
            for i in range(n):
                total += matrix[i][i]
            return total
    """), ["INDEX_OOB"], 1),

    # ======================================================================
    #  7-9: KEY_ERROR  (3 buggy)
    # ======================================================================
    ("key_error_config", textwrap.dedent("""\
        def load_config(cfg):
            host = cfg['host']
            port = cfg['port']
            return host, port
    """), ["KEY_ERROR"], 1),

    ("key_error_nested", textwrap.dedent("""\
        def get_nested(d):
            return d['level1']['level2']['value']
    """), ["KEY_ERROR"], 1),

    ("key_error_counter", textwrap.dedent("""\
        def count_words(words):
            counts = {}
            for w in words:
                counts[w] += 1
            return counts
    """), ["KEY_ERROR"], 1),

    # ======================================================================
    #  10-12: NULL_PTR  (3 buggy)
    # ======================================================================
    ("null_ptr_dict_get", textwrap.dedent("""\
        def lookup(d, key):
            val = d.get(key)
            return val.upper()
    """), ["NULL_PTR"], 1),

    ("null_ptr_find", textwrap.dedent("""\
        def find_user(users, uid):
            user = next((u for u in users if u['id'] == uid), None)
            return user['name']
    """), ["NULL_PTR"], 1),

    ("null_ptr_regex", textwrap.dedent("""\
        import re
        def extract_id(text):
            m = re.search(r'id=(\\d+)', text)
            return m.group(1)
    """), ["NULL_PTR"], 1),

    # ======================================================================
    #  13-14: TYPE_CONFUSION  (2 buggy)
    # ======================================================================
    ("type_confusion_json", textwrap.dedent("""\
        import json
        def sum_field(json_str):
            data = json.loads(json_str)
            return sum(item['val'] for item in data)
    """), ["TYPE_CONFUSION"], 1),

    ("type_confusion_iter", textwrap.dedent("""\
        def flatten(x):
            result = []
            for item in x:
                result.extend(item)
            return result
    """), ["TYPE_CONFUSION"], 1),

    # ======================================================================
    #  15-16: TYPE_ERROR  (2 buggy)
    # ======================================================================
    ("type_error_add_str_int", textwrap.dedent("""\
        def build_msg(name, count):
            return "items: " + count
    """), ["TYPE_ERROR"], 1),

    ("type_error_compare", textwrap.dedent("""\
        def clamp(value, lo, hi):
            if value < lo:
                return lo
            if value > hi:
                return hi
            return value
    """), ["TYPE_ERROR"], 1),

    # ======================================================================
    #  17-19: UNBOUND_VAR  (3 buggy)
    # ======================================================================
    ("unbound_var_cond", textwrap.dedent("""\
        def classify(x):
            if x > 0:
                label = 'positive'
            elif x < 0:
                label = 'negative'
            return label
    """), ["UNBOUND_VAR"], 1),

    ("unbound_var_loop", textwrap.dedent("""\
        def find_first_even(nums):
            for n in nums:
                if n % 2 == 0:
                    result = n
                    break
            return result
    """), ["UNBOUND_VAR"], 1),

    ("unbound_var_try", textwrap.dedent("""\
        def parse_int(s):
            try:
                val = int(s)
            except ValueError:
                pass
            return val
    """), ["UNBOUND_VAR"], 1),

    # ======================================================================
    #  20-22: VALUE_ERROR  (3 buggy)
    # ======================================================================
    ("value_error_sqrt", textwrap.dedent("""\
        import math
        def distance(x1, y1, x2, y2):
            return math.sqrt((x2 - x1) ** 2 - (y2 - y1) ** 2)
    """), ["VALUE_ERROR"], 1),

    ("value_error_log", textwrap.dedent("""\
        import math
        def log_transform(values):
            return [math.log(v) for v in values]
    """), ["VALUE_ERROR"], 1),

    ("value_error_int_parse", textwrap.dedent("""\
        def parse_port(s):
            port = int(s)
            return port
    """), ["VALUE_ERROR"], 1),

    # ======================================================================
    #  23-24: USE_AFTER_FREE  (2 buggy)
    # ======================================================================
    ("use_after_free_file", textwrap.dedent("""\
        def read_closed(path):
            f = open(path)
            f.close()
            return f.read()
    """), ["USE_AFTER_FREE"], 1),

    ("use_after_free_iter", textwrap.dedent("""\
        def consume_twice(it):
            first = list(it)
            second = list(it)
            return first, second
    """), ["USE_AFTER_FREE"], 1),

    # ======================================================================
    #  25-26: MEMORY_LEAK  (2 buggy)
    # ======================================================================
    ("memory_leak_file", textwrap.dedent("""\
        def read_all(path):
            f = open(path)
            data = f.read()
            return data
    """), ["MEMORY_LEAK"], 1),

    ("memory_leak_conn", textwrap.dedent("""\
        import sqlite3
        def query(db_path, sql):
            conn = sqlite3.connect(db_path)
            cur = conn.cursor()
            cur.execute(sql)
            rows = cur.fetchall()
            return rows
    """), ["MEMORY_LEAK"], 1),

    # ======================================================================
    #  27-28: STACK_OVERFLOW  (2 buggy)
    # ======================================================================
    ("stack_overflow_no_base", textwrap.dedent("""\
        def factorial(n):
            return n * factorial(n - 1)
    """), ["STACK_OVERFLOW"], 1),

    ("stack_overflow_mutual", textwrap.dedent("""\
        def is_even(n):
            if n == 0:
                return True
            return is_odd(n - 1)
        def is_odd(n):
            return is_even(n - 1)
    """), ["STACK_OVERFLOW"], 1),

    # ======================================================================
    #  29-31: SQL_INJECTION  (3 buggy)
    # ======================================================================
    ("sql_injection_format", textwrap.dedent("""\
        def find_user(conn, username):
            query = f"SELECT * FROM users WHERE name = '{username}'"
            return conn.execute(query).fetchall()
    """), ["SQL_INJECTION"], 1),

    ("sql_injection_concat", textwrap.dedent("""\
        def search(conn, term):
            sql = "SELECT * FROM items WHERE title LIKE '%" + term + "%'"
            return conn.execute(sql).fetchall()
    """), ["SQL_INJECTION"], 1),

    ("sql_injection_percent", textwrap.dedent("""\
        def delete_user(conn, uid):
            conn.execute("DELETE FROM users WHERE id = %s" % uid)
            conn.commit()
    """), ["SQL_INJECTION"], 1),

    # ======================================================================
    #  32-33: COMMAND_INJECTION  (2 buggy)
    # ======================================================================
    ("cmd_injection_os_system", textwrap.dedent("""\
        import os
        def ping(host):
            os.system("ping -c 1 " + host)
    """), ["COMMAND_INJECTION"], 1),

    ("cmd_injection_subprocess", textwrap.dedent("""\
        import subprocess
        def list_dir(path):
            return subprocess.check_output("ls " + path, shell=True)
    """), ["COMMAND_INJECTION"], 1),

    # ======================================================================
    #  34-35: XSS  (2 buggy)
    # ======================================================================
    ("xss_reflect", textwrap.dedent("""\
        def render_greeting(name):
            return f"<h1>Hello, {name}!</h1>"
    """), ["XSS"], 1),

    ("xss_template", textwrap.dedent("""\
        def render_comment(comment):
            return "<div class='comment'>" + comment + "</div>"
    """), ["XSS"], 1),

    # ======================================================================
    #  36-38: INTEGER_OVERFLOW  (3 buggy)
    # ======================================================================
    ("int_overflow_factorial", textwrap.dedent("""\
        import ctypes
        def factorial_32(n):
            result = ctypes.c_int32(1)
            for i in range(2, n + 1):
                result.value *= i
            return result.value
    """), ["INTEGER_OVERFLOW"], 1),

    ("int_overflow_alloc_size", textwrap.dedent("""\
        import ctypes
        def alloc_matrix(rows, cols, elem_size):
            size = ctypes.c_uint32(rows * cols * elem_size)
            return bytearray(size.value)
    """), ["INTEGER_OVERFLOW"], 1),

    ("int_overflow_midpoint", textwrap.dedent("""\
        import ctypes
        def midpoint(a, b):
            return ctypes.c_int32(a + b).value // 2
    """), ["INTEGER_OVERFLOW"], 1),

    # ======================================================================
    #  39-40: DOUBLE_FREE  (2 buggy)
    # ======================================================================
    ("double_free_ctypes", textwrap.dedent("""\
        import ctypes
        def double_release(ptr):
            ctypes.free(ptr)
            ctypes.free(ptr)
    """), ["DOUBLE_FREE"], 1),

    ("double_free_pool", textwrap.dedent("""\
        def return_twice(pool, obj):
            pool.release(obj)
            pool.release(obj)
    """), ["DOUBLE_FREE"], 1),

    # ======================================================================
    #  41-43: RACE_CONDITION  (3 buggy)
    # ======================================================================
    ("race_condition_counter", textwrap.dedent("""\
        import threading
        counter = 0
        def increment():
            global counter
            for _ in range(1000):
                counter += 1
        def run():
            threads = [threading.Thread(target=increment) for _ in range(4)]
            for t in threads: t.start()
            for t in threads: t.join()
            return counter
    """), ["RACE_CONDITION"], 1),

    ("race_check_then_act", textwrap.dedent("""\
        import os
        def safe_write(path, data):
            if not os.path.exists(path):
                with open(path, 'w') as f:
                    f.write(data)
    """), ["RACE_CONDITION"], 1),

    ("race_shared_list", textwrap.dedent("""\
        import threading
        results = []
        def worker(item):
            results.append(item * 2)
        def run(items):
            threads = [threading.Thread(target=worker, args=(i,)) for i in items]
            for t in threads: t.start()
            for t in threads: t.join()
            return results
    """), ["RACE_CONDITION"], 1),

    # ======================================================================
    #  44-45: DEADLOCK  (2 buggy)
    # ======================================================================
    ("deadlock_lock_order", textwrap.dedent("""\
        import threading
        lock_a, lock_b = threading.Lock(), threading.Lock()
        def task1():
            with lock_a:
                with lock_b:
                    return 1
        def task2():
            with lock_b:
                with lock_a:
                    return 2
    """), ["DEADLOCK"], 1),

    ("deadlock_reentrant", textwrap.dedent("""\
        import threading
        lock = threading.Lock()
        def outer():
            with lock:
                return inner()
        def inner():
            with lock:
                return 42
    """), ["DEADLOCK"], 1),

    # ======================================================================
    #  46-48: INFINITE_LOOP  (3 buggy)
    # ======================================================================
    ("infinite_loop_while", textwrap.dedent("""\
        def drain(n):
            i = 0
            while i < n:
                if i % 2 == 0:
                    continue
                i += 1
    """), ["INFINITE_LOOP"], 1),

    ("infinite_loop_wrong_var", textwrap.dedent("""\
        def find_zero(arr):
            i = 0
            while i < len(arr):
                if arr[i] == 0:
                    return i
                j = i + 1
            return -1
    """), ["INFINITE_LOOP"], 1),

    ("infinite_loop_while_true", textwrap.dedent("""\
        def read_until_done(stream):
            buf = []
            while True:
                chunk = stream.read(1024)
                buf.append(chunk)
            return b''.join(buf)
    """), ["INFINITE_LOOP"], 1),

    # ======================================================================
    #  49-50: ASSERTION_FAILURE  (2 buggy)
    # ======================================================================
    ("assertion_range", textwrap.dedent("""\
        def set_opacity(value):
            assert 0 <= value <= 1, "opacity out of range"
            return {'opacity': value}
    """), ["ASSERTION_FAILURE"], 1),

    ("assertion_type", textwrap.dedent("""\
        def process_batch(items):
            assert isinstance(items, list), "expected list"
            assert all(isinstance(i, int) for i in items), "non-int item"
            return [i * 2 for i in items]
    """), ["ASSERTION_FAILURE"], 1),

    # ======================================================================
    #  51-52: FORMAT_STRING  (2 buggy)
    # ======================================================================
    ("format_string_user", textwrap.dedent("""\
        def log_event(event_type, user_input):
            msg = "Event: %s - %s" % (event_type, user_input)
            return msg.format()
    """), ["FORMAT_STRING"], 1),

    ("format_string_template", textwrap.dedent("""\
        def render(template, context):
            return template.format(**context)
    """), ["FORMAT_STRING"], 1),

    # ======================================================================
    #  53-54: TIMING_CHANNEL  (2 buggy)
    # ======================================================================
    ("timing_channel_password", textwrap.dedent("""\
        def check_password(stored, given):
            if len(stored) != len(given):
                return False
            for a, b in zip(stored, given):
                if a != b:
                    return False
            return True
    """), ["TIMING_CHANNEL"], 1),

    ("timing_channel_token", textwrap.dedent("""\
        def verify_token(expected, provided):
            return expected == provided
    """), ["TIMING_CHANNEL"], 1),

    # ======================================================================
    #  55-60: MULTI-BUG programs  (6 buggy, multiple bugs each)
    # ======================================================================
    ("multi_div_key", textwrap.dedent("""\
        def summarize(data):
            avg = data['total'] / data['count']
            return avg
    """), ["KEY_ERROR", "DIV_ZERO"], 2),

    ("multi_oob_null", textwrap.dedent("""\
        def first_name(users):
            user = users[0]
            return user.get('name').upper()
    """), ["INDEX_OOB", "NULL_PTR"], 2),

    ("multi_sqli_xss", textwrap.dedent("""\
        def search_page(conn, query):
            rows = conn.execute("SELECT * FROM t WHERE q='" + query + "'").fetchall()
            return "<div>" + str(rows) + " for " + query + "</div>"
    """), ["SQL_INJECTION", "XSS"], 2),

    ("multi_unbound_type", textwrap.dedent("""\
        def transform(x, mode):
            if mode == 'double':
                result = x * 2
            return result + "suffix"
    """), ["UNBOUND_VAR", "TYPE_ERROR"], 2),

    ("multi_leak_injection", textwrap.dedent("""\
        import os
        def run_script(path, arg):
            f = open(path)
            content = f.read()
            os.system("bash -c '" + arg + "'")
    """), ["MEMORY_LEAK", "COMMAND_INJECTION"], 2),

    ("multi_race_overflow", textwrap.dedent("""\
        import threading, ctypes
        shared = ctypes.c_int32(0)
        def add(n):
            for _ in range(n):
                shared.value += 1
        def run():
            threads = [threading.Thread(target=add, args=(10**8,)) for _ in range(4)]
            for t in threads: t.start()
            for t in threads: t.join()
            return shared.value
    """), ["RACE_CONDITION", "INTEGER_OVERFLOW"], 2),

    # ======================================================================
    #  61-100: SAFE PROGRAMS (40 programs, no bugs)
    # ======================================================================

    # -- Safe: guarded division --
    ("safe_mean_guarded", textwrap.dedent("""\
        def mean(values):
            if not values:
                return 0.0
            return sum(values) / len(values)
    """), [], 0),

    ("safe_percentage", textwrap.dedent("""\
        def percentage(part, whole):
            if whole == 0:
                return 0.0
            return (part / whole) * 100
    """), [], 0),

    # -- Safe: guarded index --
    ("safe_first_element", textwrap.dedent("""\
        def first(lst):
            if lst:
                return lst[0]
            return None
    """), [], 0),

    ("safe_binary_search", textwrap.dedent("""\
        def binary_search(arr, target):
            lo, hi = 0, len(arr) - 1
            while lo <= hi:
                mid = (lo + hi) // 2
                if arr[mid] == target:
                    return mid
                elif arr[mid] < target:
                    lo = mid + 1
                else:
                    hi = mid - 1
            return -1
    """), [], 0),

    # -- Safe: guarded key access --
    ("safe_dict_get", textwrap.dedent("""\
        def get_value(d, key, default=None):
            return d.get(key, default)
    """), [], 0),

    ("safe_counter", textwrap.dedent("""\
        from collections import defaultdict
        def count_words(words):
            counts = defaultdict(int)
            for w in words:
                counts[w] += 1
            return dict(counts)
    """), [], 0),

    # -- Safe: null checks --
    ("safe_null_guard", textwrap.dedent("""\
        def safe_upper(d, key):
            val = d.get(key)
            if val is not None:
                return val.upper()
            return ''
    """), [], 0),

    ("safe_regex_match", textwrap.dedent("""\
        import re
        def extract_id(text):
            m = re.search(r'id=(\\d+)', text)
            return m.group(1) if m else None
    """), [], 0),

    # -- Safe: correct recursion --
    ("safe_factorial", textwrap.dedent("""\
        def factorial(n):
            if n <= 1:
                return 1
            return n * factorial(n - 1)
    """), [], 0),

    ("safe_fib", textwrap.dedent("""\
        def fib(n):
            if n <= 1:
                return n
            a, b = 0, 1
            for _ in range(2, n + 1):
                a, b = b, a + b
            return b
    """), [], 0),

    # -- Safe: parameterized queries --
    ("safe_sql_param", textwrap.dedent("""\
        def find_user(conn, username):
            return conn.execute("SELECT * FROM users WHERE name = ?", (username,)).fetchall()
    """), [], 0),

    ("safe_sql_insert", textwrap.dedent("""\
        def insert_item(conn, name, price):
            conn.execute("INSERT INTO items (name, price) VALUES (?, ?)", (name, price))
            conn.commit()
    """), [], 0),

    # -- Safe: escaped output --
    ("safe_html_escape", textwrap.dedent("""\
        from html import escape
        def render_greeting(name):
            return f"<h1>Hello, {escape(name)}!</h1>"
    """), [], 0),

    ("safe_html_template", textwrap.dedent("""\
        from html import escape
        def render_comment(comment):
            return "<div class='comment'>" + escape(comment) + "</div>"
    """), [], 0),

    # -- Safe: subprocess without shell --
    ("safe_subprocess", textwrap.dedent("""\
        import subprocess
        def list_dir(path):
            return subprocess.check_output(["ls", path])
    """), [], 0),

    ("safe_subprocess_run", textwrap.dedent("""\
        import subprocess
        def ping(host):
            return subprocess.run(["ping", "-c", "1", host], capture_output=True)
    """), [], 0),

    # -- Safe: with-statement (no leak) --
    ("safe_file_with", textwrap.dedent("""\
        def read_file(path):
            with open(path) as f:
                return f.read()
    """), [], 0),

    ("safe_db_with", textwrap.dedent("""\
        import sqlite3
        def query(db_path, sql, params):
            with sqlite3.connect(db_path) as conn:
                return conn.execute(sql, params).fetchall()
    """), [], 0),

    # -- Safe: threading with lock --
    ("safe_counter_locked", textwrap.dedent("""\
        import threading
        lock = threading.Lock()
        counter = 0
        def increment():
            global counter
            with lock:
                counter += 1
    """), [], 0),

    ("safe_lock_order", textwrap.dedent("""\
        import threading
        lock_a, lock_b = threading.Lock(), threading.Lock()
        def task():
            with lock_a:
                with lock_b:
                    return 42
    """), [], 0),

    # -- Safe: constant-time compare --
    ("safe_hmac_compare", textwrap.dedent("""\
        import hmac
        def verify_token(expected, provided):
            return hmac.compare_digest(expected, provided)
    """), [], 0),

    # -- Safe: math with domain checks --
    ("safe_sqrt", textwrap.dedent("""\
        import math
        def safe_sqrt(x):
            if x < 0:
                return float('nan')
            return math.sqrt(x)
    """), [], 0),

    ("safe_log", textwrap.dedent("""\
        import math
        def safe_log(values):
            return [math.log(v) if v > 0 else float('-inf') for v in values]
    """), [], 0),

    # -- Safe: proper loop termination --
    ("safe_while_loop", textwrap.dedent("""\
        def count_up(n):
            i = 0
            while i < n:
                i += 1
            return i
    """), [], 0),

    ("safe_sentinel_loop", textwrap.dedent("""\
        def read_until_done(stream):
            buf = []
            while True:
                chunk = stream.read(1024)
                if not chunk:
                    break
                buf.append(chunk)
            return b''.join(buf)
    """), [], 0),

    # -- Safe: proper variable binding --
    ("safe_classify", textwrap.dedent("""\
        def classify(x):
            if x > 0:
                label = 'positive'
            elif x < 0:
                label = 'negative'
            else:
                label = 'zero'
            return label
    """), [], 0),

    ("safe_find_even", textwrap.dedent("""\
        def find_first_even(nums):
            result = None
            for n in nums:
                if n % 2 == 0:
                    result = n
                    break
            return result
    """), [], 0),

    # -- Safe: type-safe operations --
    ("safe_stringify", textwrap.dedent("""\
        def build_msg(name, count):
            return "items: " + str(count)
    """), [], 0),

    ("safe_typed_add", textwrap.dedent("""\
        def add(a: int, b: int) -> int:
            return a + b
    """), [], 0),

    # -- Safe: assertion with valid precondition doc --
    ("safe_assert_range", textwrap.dedent("""\
        def clamp_opacity(value):
            clamped = max(0.0, min(1.0, value))
            assert 0 <= clamped <= 1
            return clamped
    """), [], 0),

    # -- Safe: data processing pipelines --
    ("safe_filter_map", textwrap.dedent("""\
        def positive_squares(nums):
            return [x * x for x in nums if x > 0]
    """), [], 0),

    ("safe_group_by", textwrap.dedent("""\
        from collections import defaultdict
        def group_by_key(pairs):
            groups = defaultdict(list)
            for k, v in pairs:
                groups[k].append(v)
            return dict(groups)
    """), [], 0),

    ("safe_merge_sorted", textwrap.dedent("""\
        def merge(a, b):
            result, i, j = [], 0, 0
            while i < len(a) and j < len(b):
                if a[i] <= b[j]:
                    result.append(a[i])
                    i += 1
                else:
                    result.append(b[j])
                    j += 1
            result.extend(a[i:])
            result.extend(b[j:])
            return result
    """), [], 0),

    ("safe_transpose", textwrap.dedent("""\
        def transpose(matrix):
            if not matrix:
                return []
            return [list(row) for row in zip(*matrix)]
    """), [], 0),

    # -- Safe: web / string handling --
    ("safe_url_encode", textwrap.dedent("""\
        from urllib.parse import quote
        def build_url(base, param):
            return f"{base}?q={quote(param)}"
    """), [], 0),

    ("safe_json_serialize", textwrap.dedent("""\
        import json
        def to_json(data):
            return json.dumps(data, default=str)
    """), [], 0),

    # -- Safe: ML-style pipeline --
    ("safe_normalize_vec", textwrap.dedent("""\
        import math
        def normalize(vec):
            norm = math.sqrt(sum(x * x for x in vec))
            if norm == 0:
                return vec[:]
            return [x / norm for x in vec]
    """), [], 0),

    ("safe_softmax", textwrap.dedent("""\
        import math
        def softmax(logits):
            max_l = max(logits)
            exps = [math.exp(l - max_l) for l in logits]
            total = sum(exps)
            return [e / total for e in exps]
    """), [], 0),

    ("safe_minibatch", textwrap.dedent("""\
        def minibatches(data, batch_size):
            return [data[i:i+batch_size] for i in range(0, len(data), batch_size)]
    """), [], 0),

    ("safe_moving_average", textwrap.dedent("""\
        def moving_average(data, window):
            if window <= 0 or not data:
                return []
            result = []
            for i in range(len(data) - window + 1):
                result.append(sum(data[i:i+window]) / window)
            return result
    """), [], 0),
]

# ---------------------------------------------------------------------------
# Quick self-check: counts
# ---------------------------------------------------------------------------
_buggy = sum(1 for _, _, bugs, _ in BUG_PROGRAMS if bugs)
_safe = sum(1 for _, _, bugs, _ in BUG_PROGRAMS if not bugs)
assert len(BUG_PROGRAMS) == 100, f"Expected 100 programs, got {len(BUG_PROGRAMS)}"
assert _buggy == 60, f"Expected 60 buggy, got {_buggy}"
assert _safe == 40, f"Expected 40 safe, got {_safe}"
