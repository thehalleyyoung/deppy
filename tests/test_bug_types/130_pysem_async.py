"""Python semantics: async/await patterns — NULL_PTR, USE_AFTER_FREE."""

BUG_TYPE = "NULL_PTR"
BUG_DESC = "Async coroutines returning None and unawaited access"

EXAMPLES = [
    (
        "async_none_return",
        # buggy: async function may return None, caller dereferences
        '''\
async def fetch_user(user_id):
    if user_id < 0:
        return None
    return {"name": "Alice", "id": user_id}

async def greet(user_id):
    user = await fetch_user(user_id)
    return user["name"]
''',
        # safe: guard None
        '''\
async def fetch_user(user_id):
    if user_id < 0:
        return None
    return {"name": "Alice", "id": user_id}

async def greet(user_id):
    user = await fetch_user(user_id)
    if user is not None:
        return user["name"]
    return "Unknown"
''',
        "fetch_user returns None for negative id; user['name'] on None",
    ),
    (
        "async_ctx_none",
        # buggy: async context manager yields None on error
        '''\
class AsyncSession:
    async def __aenter__(self):
        self.conn = None
        return self
    async def __aexit__(self, *args):
        pass

async def run_query(query):
    async with AsyncSession() as session:
        result = session.conn.execute(query)
    return result
''',
        # safe: check conn
        '''\
class AsyncSession:
    async def __aenter__(self):
        self.conn = None
        return self
    async def __aexit__(self, *args):
        pass

async def run_query(query):
    async with AsyncSession() as session:
        if session.conn is not None:
            result = session.conn.execute(query)
        else:
            result = None
    return result
''',
        "session.conn is None; .execute on None",
    ),
]
