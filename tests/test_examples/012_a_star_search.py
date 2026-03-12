"""A* pathfinding on a weighted grid.

Bug: The heuristic function returns manhattan_distance * 5 (inadmissible),
which causes A* to find suboptimal paths by massively over-estimating the
remaining cost, greedily preferring cells closer to the goal.
"""

CORRECT = r"""
import heapq

def a_star_search(grid):
    rows = len(grid)
    cols = len(grid[0])
    start = (0, 0)
    goal = (rows - 1, cols - 1)

    if grid[start[0]][start[1]] == 0 or grid[goal[0]][goal[1]] == 0:
        return None

    def heuristic(pos):
        # Manhattan distance (admissible for 4-directional movement)
        return abs(pos[0] - goal[0]) + abs(pos[1] - goal[1])

    # g_score[node] = cost of cheapest path from start to node
    g_score = {}
    g_score[start] = grid[start[0]][start[1]]

    # f_score[node] = g_score[node] + heuristic(node)
    f_score = {}
    f_score[start] = g_score[start] + heuristic(start)

    # Priority queue: (f_score, counter, node)
    counter = 0
    open_set = [(f_score[start], counter, start)]
    came_from = {}
    closed_set = set()

    while open_set:
        current_f, _, current = heapq.heappop(open_set)

        if current in closed_set:
            continue

        if current == goal:
            # Reconstruct path
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            path.reverse()
            total_cost = g_score[goal]
            return (total_cost, path)

        closed_set.add(current)

        # Explore neighbors (4-directional)
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            nr, nc = current[0] + dr, current[1] + dc
            neighbor = (nr, nc)

            if nr < 0 or nr >= rows or nc < 0 or nc >= cols:
                continue
            if grid[nr][nc] == 0:
                continue
            if neighbor in closed_set:
                continue

            tentative_g = g_score[current] + grid[nr][nc]

            if tentative_g < g_score.get(neighbor, float('inf')):
                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                f = tentative_g + heuristic(neighbor)
                f_score[neighbor] = f
                counter += 1
                heapq.heappush(open_set, (f, counter, neighbor))

    return None  # No path found

grid = GRID
result = a_star_search(grid)
"""

BUGGY = r"""
import heapq

def a_star_search(grid):
    rows = len(grid)
    cols = len(grid[0])
    start = (0, 0)
    goal = (rows - 1, cols - 1)

    if grid[start[0]][start[1]] == 0 or grid[goal[0]][goal[1]] == 0:
        return None

    def heuristic(pos):
        # BUG: manhattan distance * 5 (grossly inadmissible heuristic)
        # This massively overestimates the remaining cost, causing A*
        # to greedily prefer cells closer to the goal even if they are
        # expensive, and to prematurely close cheaper but longer routes
        return (abs(pos[0] - goal[0]) + abs(pos[1] - goal[1])) * 5

    # g_score[node] = cost of cheapest path from start to node
    g_score = {}
    g_score[start] = grid[start[0]][start[1]]

    # f_score[node] = g_score[node] + heuristic(node)
    f_score = {}
    f_score[start] = g_score[start] + heuristic(start)

    # Priority queue: (f_score, counter, node)
    counter = 0
    open_set = [(f_score[start], counter, start)]
    came_from = {}
    closed_set = set()

    while open_set:
        current_f, _, current = heapq.heappop(open_set)

        if current in closed_set:
            continue

        if current == goal:
            # Reconstruct path
            path = [current]
            while current in came_from:
                current = came_from[current]
                path.append(current)
            path.reverse()
            total_cost = g_score[goal]
            return (total_cost, path)

        closed_set.add(current)

        # Explore neighbors (4-directional)
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            nr, nc = current[0] + dr, current[1] + dc
            neighbor = (nr, nc)

            if nr < 0 or nr >= rows or nc < 0 or nc >= cols:
                continue
            if grid[nr][nc] == 0:
                continue
            if neighbor in closed_set:
                continue

            tentative_g = g_score[current] + grid[nr][nc]

            if tentative_g < g_score.get(neighbor, float('inf')):
                came_from[neighbor] = current
                g_score[neighbor] = tentative_g
                f = tentative_g + heuristic(neighbor)
                f_score[neighbor] = f
                counter += 1
                heapq.heappush(open_set, (f, counter, neighbor))

    return None  # No path found

grid = GRID
result = a_star_search(grid)
"""


def SPEC(GRID, result):
    """Verify A* result: valid path, correct cost accounting, and optimality."""
    import heapq as _heapq

    rows = len(GRID)
    cols = len(GRID[0])

    if result is None:
        return False  # Our grids are always passable

    total_cost, path = result

    if not isinstance(path, list) or len(path) == 0:
        return False

    # (1) Path starts at (0,0) and ends at (rows-1, cols-1)
    if path[0] != (0, 0):
        return False
    if path[-1] != (rows - 1, cols - 1):
        return False

    # (2) Each step moves to an adjacent non-zero cell
    for i in range(1, len(path)):
        r1, c1 = path[i - 1]
        r2, c2 = path[i]
        if abs(r1 - r2) + abs(c1 - c2) != 1:
            return False
        if r2 < 0 or r2 >= rows or c2 < 0 or c2 >= cols:
            return False
        if GRID[r2][c2] == 0:
            return False

    # (3) Total cost is sum of cell costs along path
    computed_cost = sum(GRID[r][c] for r, c in path)
    if abs(computed_cost - total_cost) > 1e-9:
        return False

    # (4) Path cost is optimal — run Dijkstra as reference
    start = (0, 0)
    goal = (rows - 1, cols - 1)
    dist = {}
    dist[start] = GRID[start[0]][start[1]]
    pq = [(dist[start], start)]

    while pq:
        d, u = _heapq.heappop(pq)
        if d > dist.get(u, float('inf')):
            continue
        if u == goal:
            break
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            nr, nc = u[0] + dr, u[1] + dc
            if 0 <= nr < rows and 0 <= nc < cols and GRID[nr][nc] != 0:
                nd = d + GRID[nr][nc]
                if nd < dist.get((nr, nc), float('inf')):
                    dist[(nr, nc)] = nd
                    _heapq.heappush(pq, (nd, (nr, nc)))

    optimal_cost = dist.get(goal, float('inf'))
    if abs(total_cost - optimal_cost) > 1e-9:
        return False

    return True


BUG_DESC = (
    "The heuristic function returns manhattan_distance * 5, making it "
    "grossly inadmissible. This causes A* to massively overestimate "
    "remaining costs, greedily preferring cells closer to the goal and "
    "finding suboptimal paths instead of the true shortest path."
)


def _generate_grid():
    import random
    n = random.randint(6, 8)
    # Costs 1-9 with wide variation so cheaper detours exist
    # No zeros, so path always exists
    grid = [[random.randint(1, 9) for _ in range(n)] for _ in range(n)]
    return grid


INPUT_OVERRIDES = {
    "GRID": _generate_grid,
}
