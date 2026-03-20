# Real-World Usage: The Holy Grail in Practice

## What follows are 6 realistic scenarios showing what it looks like when
## hybrid dependent algebraic-geometric typing with controlled oracles
## is applied to REAL codebases — large, multi-library, not-all-Python.

---

## EXAMPLE 1: Data Pipeline (Python + Pandas + SQL + dbt)

### The problem
An LLM generates a Pandas transformation for a dbt-managed data warehouse.
The generated code references column names that don't exist, silently drops
NULLs the business logic requires to keep, and the SQL view and the Python
transformation disagree on the output schema.

### What the developer writes

```python
# etl/transform_orders.py
from deppy.hybrid import spec, hole, guarantee, assume, check
from deppy.hybrid.theory_library import pandas_theory, sql_theory

@guarantee("""
    Output DataFrame has columns: order_id (int), customer_id (int),
    total_usd (float >= 0), status (one of 'pending','shipped','delivered'),
    created_at (datetime, timezone-aware).
    No rows are dropped — output has same row count as input.
    NULL handling: total_usd NULLs become 0.0, all other NULLs preserved.
""")
def transform_orders(raw_orders: pd.DataFrame, exchange_rates: pd.DataFrame) -> pd.DataFrame:
    assume("raw_orders has columns: id, cust_id, amount_local, currency, status, created")
    assume("exchange_rates has columns: currency_code, rate_to_usd, as_of_date")

    # Concrete code: the join
    merged = raw_orders.merge(
        exchange_rates,
        left_on="currency",
        right_on="currency_code",
        how="left"
    )

    # NL hole: the currency conversion
    converted = hole("""
        Compute total_usd = amount_local * rate_to_usd.
        If rate_to_usd is NULL (unknown currency), use 1.0 as fallback.
        If amount_local is NULL, total_usd should be 0.0.
    """)

    # Concrete code: rename and select
    result = converted.rename(columns={"id": "order_id", "cust_id": "customer_id"})
    result = result[["order_id", "customer_id", "total_usd", "status", "created_at"]]

    check("result.shape[0] == raw_orders.shape[0]")  # no rows dropped
    check("result['total_usd'].isna().sum() == 0")    # no NULL totals
    check("result['status'].isin(['pending','shipped','delivered']).all()")

    return result
```

### What `deppy hybrid compile` produces

```
═══════════════════════════════════════════════════════════════
 HYBRID TYPE ANALYSIS: etl/transform_orders.py
═══════════════════════════════════════════════════════════════

THEORY PACKS LOADED:
  ✓ pandas_theory (v2.1): DataFrame schema tracking, merge semantics, NULL propagation
  ✓ sql_theory (v1.0): dbt model schema, column existence, type compatibility

LAYER ANALYSIS:

  INTENT layer:
    @guarantee parsed → 7 claims extracted:
      1. "output has column order_id : int"           → STRUCTURAL (schema check)
      2. "output has column total_usd : float >= 0"   → STRUCTURAL (schema + Z3)
      3. "status is one of pending/shipped/delivered"  → STRUCTURAL (enum check)
      4. "created_at is timezone-aware datetime"       → STRUCTURAL (dtype check)
      5. "no rows are dropped"                         → STRUCTURAL (shape equality)
      6. "total_usd NULLs become 0.0"                 → STRUCTURAL (isna check)
      7. "all other NULLs preserved"                   → SEMANTIC  (behavior judgment)

  STRUCTURAL layer (Z3_PROVEN):
    ✓ Schema after merge: pandas_theory infers merged has columns
      {id, cust_id, amount_local, currency, status, created,
       currency_code, rate_to_usd, as_of_date}
    ✓ rename(id→order_id, cust_id→customer_id): column tracking updated
    ✓ select 5 columns: all exist in renamed frame ← Z3: set membership
    ✓ merge(how='left'): row count ≥ raw_orders.shape[0]
      ⚠ OBSTRUCTION: left join can INCREASE row count if exchange_rates
        has duplicate currency_code values!
        H¹ generator: (merge_site, return_site) cocycle ≠ 0
        → check("no rows dropped") may FAIL

  SEMANTIC layer (LLM_JUDGED, conf 0.89):
    ✓ "all other NULLs preserved" — oracle judges the transformation preserves NULLs
      in customer_id, status, created_at columns

  HOLE SYNTHESIS:
    "Compute total_usd = amount_local * rate_to_usd..."
    → Synthesized:
        converted = merged.copy()
        converted['rate_to_usd'] = converted['rate_to_usd'].fillna(1.0)
        converted['amount_local'] = converted['amount_local'].fillna(0.0)
        converted['total_usd'] = converted['amount_local'] * converted['rate_to_usd']
    → Structural check: ✓ (total_usd column exists, float dtype, no NULLs)
    → Semantic check: ✓ (oracle: "correctly handles NULL fallbacks", conf 0.93)

  ⚠ CROSS-LANGUAGE CHECK (dbt model):
    Loaded dbt schema from models/orders.yml:
      order_id: integer, not_null
      customer_id: integer
      total_usd: numeric, not_null
      status: varchar, accepted_values: [pending, shipped, delivered]
      created_at: timestamp with time zone, not_null
    
    Python output schema vs dbt schema:
    ✓ order_id: int ↔ integer          — compatible
    ✓ total_usd: float ↔ numeric       — compatible
    ✓ status: str ↔ varchar             — compatible
    ⚠ created_at: datetime ↔ timestamp with time zone
      Python column is timezone-NAIVE after merge!
      H¹(Layer) ≠ 0: INTENT says "timezone-aware" but CODE produces naive datetime
      → STRUCTURAL_HALLUCINATION at layer pair (INTENT, CODE)

TRUST REPORT:
  3 claims Z3_PROVEN, 1 claim LLM_JUDGED, 1 OBSTRUCTION (left join cardinality),
  1 HALLUCINATION (timezone-naive datetime)
  Overall: CONTRADICTED until obstructions resolved

REMEDIATION:
  1. Add: assume("exchange_rates has unique currency_code") or deduplicate before merge
  2. Add: converted['created_at'] = pd.to_datetime(converted['created'], utc=True)
  3. After fixes, re-run → expected: H¹ = 0, trust = LLM_JUDGED
```

### Why this matters
The LLM-generated hole was correct. But the system caught TWO bugs the LLM
AND the human would have missed: the left join cardinality issue (structural,
Z3-provable) and the timezone mismatch between Python and dbt (cross-language
layer inconsistency, H¹ ≠ 0). No existing tool catches both.

---

## EXAMPLE 2: ML Training Pipeline (Python + PyTorch + CUDA kernels + bash)

### The problem
An LLM generates a custom attention mechanism. It hallucinates a PyTorch API
that doesn't exist in the installed version, gets tensor shapes wrong (the
classic (B,T,C) vs (B,C,T) confusion), and the training script's
hyperparameters don't match the model's expectations.

### What the developer writes

```python
# models/multi_head_attention.py
from deppy.hybrid import spec, hole, guarantee, check, assume
from deppy.hybrid.theory_library import torch_theory

@guarantee("""
    Implements scaled dot-product multi-head attention.
    Input: x of shape (batch, seq_len, d_model).
    Output: same shape (batch, seq_len, d_model).
    Number of heads divides d_model evenly.
    No in-place mutation of input tensor.
""")
class MultiHeadAttention(nn.Module):
    def __init__(self, d_model: int, n_heads: int, dropout: float = 0.1):
        super().__init__()
        assume("d_model % n_heads == 0")
        self.d_model = d_model
        self.n_heads = n_heads
        self.d_k = d_model // n_heads

        self.W_q = nn.Linear(d_model, d_model)
        self.W_k = nn.Linear(d_model, d_model)
        self.W_v = nn.Linear(d_model, d_model)
        self.W_o = nn.Linear(d_model, d_model)
        self.dropout = nn.Dropout(dropout)

    def forward(self, x: torch.Tensor, mask: Optional[torch.Tensor] = None) -> torch.Tensor:
        batch, seq_len, _ = x.shape
        check("x.shape[-1] == self.d_model")

        Q = self.W_q(x).view(batch, seq_len, self.n_heads, self.d_k).transpose(1, 2)
        K = self.W_k(x).view(batch, seq_len, self.n_heads, self.d_k).transpose(1, 2)
        V = self.W_v(x).view(batch, seq_len, self.n_heads, self.d_k).transpose(1, 2)

        # shape: Q,K,V are (batch, n_heads, seq_len, d_k)
        scores = hole("compute scaled dot-product attention scores from Q and K")
        
        if mask is not None:
            scores = scores.masked_fill(mask == 0, float('-inf'))

        attn_weights = hole("apply softmax and dropout to scores")

        context = torch.matmul(attn_weights, V)  # (batch, n_heads, seq_len, d_k)
        context = context.transpose(1, 2).contiguous().view(batch, seq_len, self.d_model)

        return self.W_o(context)
```

### What `deppy hybrid compile` produces

```
═══════════════════════════════════════════════════════════════
 HYBRID TYPE ANALYSIS: models/multi_head_attention.py
═══════════════════════════════════════════════════════════════

THEORY PACK: torch_theory (v2.1)
  Tensor shape algebra loaded: matmul, view, transpose, softmax rules
  API registry: PyTorch 2.1.0 (1,847 verified functions)

SHAPE TRACKING (dependent types over tensor dimensions):
  x         : Tensor[batch, seq_len, d_model]
  W_q(x)    : Tensor[batch, seq_len, d_model]   ← Linear(d_model, d_model)
  .view()   : Tensor[batch, seq_len, n_heads, d_k]  where d_k = d_model // n_heads
    Z3: batch * seq_len * n_heads * d_k == batch * seq_len * d_model  ✓
    Z3: d_model % n_heads == 0  ✓ (from assume)
  .transpose(1,2): Tensor[batch, n_heads, seq_len, d_k]  ✓

HOLE 1: "compute scaled dot-product attention scores from Q and K"
  Context: Q : Tensor[batch, n_heads, seq_len, d_k]
           K : Tensor[batch, n_heads, seq_len, d_k]
  Expected output used in: masked_fill → softmax → matmul with V
  Inferred shape: Tensor[batch, n_heads, seq_len, seq_len]
  
  Synthesized: scores = torch.matmul(Q, K.transpose(-2, -1)) / math.sqrt(self.d_k)

  Shape verification (Z3):
    matmul([b,h,s,d], [b,h,d,s]) → [b,h,s,s]  ✓
    Division by scalar preserves shape            ✓
  Semantic verification (oracle, conf 0.96):
    "This is standard scaled dot-product attention"  ✓

HOLE 2: "apply softmax and dropout to scores"
  Context: scores : Tensor[batch, n_heads, seq_len, seq_len]
  Expected: same shape, values in [0,1], rows sum to 1

  Synthesized: attn_weights = self.dropout(F.softmax(scores, dim=-1))

  Shape verification: softmax preserves shape, dropout preserves shape  ✓
  Semantic verification: "softmax on last dim gives attention distribution"  ✓

  ⚠ API CHECK: F.softmax exists in torch 2.1.0  ✓
  (If LLM had generated torch.nn.functional.scaled_dot_product_attention
   which requires torch >= 2.0 — system would flag version compatibility)

CROSS-FILE CHECK (train.py):
  Loaded train.py configuration:
    model = MultiHeadAttention(d_model=512, n_heads=8, dropout=0.1)
    x = torch.randn(32, 128, 512)
  
  Z3: 512 % 8 == 0  ✓
  Shape: input (32, 128, 512) → output (32, 128, 512)  ✓

LEAN:
  theorem shape_preserved :
    ∀ b s d h, d % h = 0 →
    (multi_head_attn b s d h).shape = (b, s, d)            → LEAN_VERIFIED (omega)
  theorem attention_scores_shape :
    ∀ b h s d, matmul_shape (b,h,s,d) (b,h,d,s) = (b,h,s,s)  → LEAN_VERIFIED (simp)

TRUST: Z3_PROVEN (shapes) ∧ LLM_JUDGED (semantics) = LLM_JUDGED
H¹ = 0 — no intent-implementation gap
```

---

## EXAMPLE 3: Web API + Frontend (Python FastAPI + TypeScript React + OpenAPI)

### The problem
Backend and frontend are developed separately. The LLM generates a React
component that calls an API endpoint with the wrong field names, expects a
response field that was renamed last sprint, and handles errors with a
status code the backend never returns.

### What the developer writes

```python
# backend/routes/users.py
from deppy.hybrid import guarantee, check
from deppy.hybrid.theory_library import fastapi_theory

@app.get("/api/users/{user_id}")
@guarantee("""
    Returns UserResponse JSON with fields:
      id (int), email (string, valid email), display_name (string, 1-100 chars),
      role (one of 'admin','editor','viewer'), created_at (ISO 8601 string).
    Returns 404 if user not found (body: {"detail": "User not found"}).
    Returns 403 if caller lacks permission (body: {"detail": "Forbidden"}).
    Never returns 500 for valid user_id inputs.
""")
async def get_user(user_id: int, current_user: User = Depends(get_current_user)):
    user = await db.users.get(user_id)
    if not user:
        raise HTTPException(status_code=404, detail="User not found")
    if not can_view(current_user, user):
        raise HTTPException(status_code=403, detail="Forbidden")
    return UserResponse.from_orm(user)
```

```typescript
// frontend/components/UserProfile.tsx
// @deppy:guarantee("displays user profile from /api/users/{id}, handles loading+error states")
// @deppy:assume("backend /api/users/{id} returns UserResponse as specified in backend/routes/users.py")

export function UserProfile({ userId }: { userId: number }) {
    const { data, error, isLoading } = useSWR(`/api/users/${userId}`, fetcher);
    
    if (isLoading) return <Spinner />;
    if (error?.status === 404) return <NotFound message="User not found" />;
    if (error?.status === 403) return <Forbidden />;
    if (error) return <GenericError />;
    
    // @deppy:check("data has fields: id, email, display_name, role, created_at")
    return (
        <div>
            <h1>{data.display_name}</h1>
            <p>{data.email}</p>
            <RoleBadge role={data.role} />
            <time>{new Date(data.created_at).toLocaleDateString()}</time>
        </div>
    );
}
```

### What `deppy hybrid compile` produces

```
═══════════════════════════════════════════════════════════════
 CROSS-LANGUAGE HYBRID TYPE ANALYSIS
 backend/routes/users.py ↔ frontend/components/UserProfile.tsx
═══════════════════════════════════════════════════════════════

THEORY PACKS:
  ✓ fastapi_theory: route extraction, response model inference, HTTP status codes
  ✓ typescript_theory: TSX type extraction, SWR response typing
  ✓ openapi_theory: schema bridge between Python Pydantic and TypeScript interfaces

BACKEND ANALYSIS (Python):
  Route: GET /api/users/{user_id: int}
  Response type (inferred from UserResponse + Pydantic):
    { id: int, email: str, display_name: str, role: Literal['admin','editor','viewer'],
      created_at: str }
  Error responses: 404 {"detail": "User not found"}, 403 {"detail": "Forbidden"}
  Guarantee claim "never 500 for valid input":
    → SEMANTIC (oracle): conf 0.87 — depends on db.users.get not throwing

FRONTEND ANALYSIS (TypeScript):
  Component reads: data.display_name, data.email, data.role, data.created_at
  Error handling: 404, 403, generic
  Missing field access: data.id (declared in guarantee but never used — warning only)

CROSS-LANGUAGE LAYER CHECK:

  ✓ Field names match:
    Backend UserResponse.display_name ↔ Frontend data.display_name  ✓
    Backend UserResponse.email ↔ Frontend data.email                ✓
    Backend UserResponse.role ↔ Frontend data.role                  ✓
    Backend UserResponse.created_at ↔ Frontend data.created_at      ✓

  ✓ Error codes match:
    Backend raises 404 ↔ Frontend handles error?.status === 404     ✓
    Backend raises 403 ↔ Frontend handles error?.status === 403     ✓

  ✓ No hallucinated fields:
    Frontend doesn't access any field not in UserResponse            ✓

  ✓ No unhandled errors:
    Backend can return 404, 403 — both handled by frontend           ✓

  ⚠ DRIFT WARNING:
    If backend UserResponse ever adds/removes/renames a field,
    the cross-language cocycle breaks → H¹(Language×Layer) ≠ 0
    Recommendation: generate TypeScript interface from Pydantic model

H¹ = 0 — backend and frontend agree on the contract
```

### If the LLM had hallucinated

```
Suppose the LLM generated the frontend using `data.name` instead of
`data.display_name` (a common LLM hallucination — using the "obvious" name):

  ⚠ STRUCTURAL HALLUCINATION:
    Frontend accesses data.name — field does not exist in UserResponse
    UserResponse fields: {id, email, display_name, role, created_at}
    'name' ∉ {id, email, display_name, role, created_at}
    → H¹(Language, HybridTy) ≠ 0 at site (UserProfile.return, STRUCTURAL)

  ⚠ Suggested fix: data.name → data.display_name
```

---

## EXAMPLE 4: Financial Compliance (Python + NumPy + Regulatory NL Spec)

### The problem
A regulation says "the risk-weighted capital ratio must not fall below 8%."
The LLM generates the calculation, but uses the wrong formula for
risk-weighted assets (confuses Basel II and Basel III), and silently
converts basis points to percentages incorrectly.

### What the developer writes

```python
# risk/capital_ratio.py
from deppy.hybrid import spec, guarantee, hole, check, assume, given

given("""
    Basel III Capital Requirements (CRR Article 92):
    - Common Equity Tier 1 (CET1) ratio ≥ 4.5%
    - Tier 1 capital ratio ≥ 6%
    - Total capital ratio ≥ 8%
    - Risk-weighted assets (RWA) = Σ(exposure_i × risk_weight_i)
    - Risk weights: sovereign 0%, corporate 100%, retail 75%, mortgage 35%
    Source: EU Regulation 575/2013
""")

@guarantee("""
    Computes Basel III total capital ratio = total_capital / RWA.
    Returns ratio as a decimal (0.08 = 8%, NOT 8.0).
    RWA uses Basel III standard approach risk weights.
    All inputs in same currency (no FX conversion needed).
""")
def compute_capital_ratio(
    total_capital: float,
    exposures: np.ndarray,         # shape (n_exposures,)
    asset_classes: np.ndarray,     # shape (n_exposures,) values in {0,1,2,3}
) -> float:
    assume("total_capital > 0")
    assume("exposures.shape == asset_classes.shape")
    assume("all(asset_classes[i] in {0,1,2,3} for i in range(len(asset_classes)))")

    # Basel III standard risk weights
    RISK_WEIGHTS = {0: 0.0, 1: 1.0, 2: 0.75, 3: 0.35}  # sovereign, corporate, retail, mortgage

    rwa = hole("compute risk-weighted assets using Basel III standard approach weights")

    check("rwa >= 0")
    check("rwa <= exposures.sum()")  # RWA can't exceed total exposure (max weight is 1.0)

    ratio = total_capital / rwa if rwa > 0 else float('inf')

    check("ratio is a decimal, not a percentage (e.g., 0.08 not 8.0)")

    return ratio

@spec("""
    Return True if the institution meets ALL Basel III minimum capital ratios:
    CET1 ≥ 4.5%, Tier1 ≥ 6%, Total ≥ 8%.
    This is a REGULATORY REQUIREMENT — false negatives are compliance violations.
""")
def meets_basel3_minimums(cet1_ratio: float, tier1_ratio: float, total_ratio: float) -> bool:
    ...
```

### What `deppy hybrid compile` produces

```
═══════════════════════════════════════════════════════════════
 HYBRID TYPE ANALYSIS: risk/capital_ratio.py
 REGULATORY MODE: Basel III (EU 575/2013)
═══════════════════════════════════════════════════════════════

GIVEN (regulatory axioms imported):
  Basel III risk weights loaded:
    sovereign=0%, corporate=100%, retail=75%, mortgage=35%
  Source: EU Regulation 575/2013, Article 92
  Trust: HUMAN_AUTHORED (regulatory text)

HOLE: "compute risk-weighted assets using Basel III standard approach"
  Context: exposures (n,), asset_classes (n,), RISK_WEIGHTS dict
  
  Synthesized:
    weights = np.array([RISK_WEIGHTS[c] for c in asset_classes])
    rwa = np.sum(exposures * weights)
  
  Structural verification (Z3):
    ✓ weights.shape == exposures.shape (same length)
    ✓ all weights in [0.0, 1.0] (from RISK_WEIGHTS values)
    ✓ rwa = dot(exposures, weights) ≥ 0 (non-negative exposures × non-negative weights)
    ✓ rwa ≤ sum(exposures) (since max weight is 1.0)

  Regulatory verification (oracle + given):
    ✓ Risk weights match Basel III Article 92 standard approach
    ✓ Formula is RWA = Σ(exposure_i × risk_weight_i) — matches CRR definition
    ⚠ NOTE: This is the STANDARD approach. IRB approach uses different weights.
      Oracle confidence: 0.94

  Anti-hallucination check:
    ✓ No Basel II formulas used (Basel II had different retail weight: 75% same, but
      Basel II securitization weights differ — not relevant here)
    ✓ No confusion between basis points and percentages in the ratio
    ✓ Ratio is decimal (0.08), not percentage (8.0) — verified by check()

SPEC SYNTHESIS: meets_basel3_minimums
  Synthesized body:
    return cet1_ratio >= 0.045 and tier1_ratio >= 0.06 and total_ratio >= 0.08

  ✓ Thresholds match Article 92: CET1 4.5%, T1 6%, Total 8%
  ✓ Comparison uses >= (not >, which would be wrong)
  ✓ Values are decimals, not percentages

LEAN:
  theorem rwa_bounded :
    ∀ exp wts, (∀ i, 0 ≤ wts[i] ∧ wts[i] ≤ 1) →
    0 ≤ dot exp wts ∧ dot exp wts ≤ sum exp     → LEAN_VERIFIED

  theorem ratio_correct_unit :
    ∀ cap rwa, rwa > 0 → cap / rwa ∈ [0, ∞)
    ∧ (cap / rwa ≥ 0.08 ↔ cap ≥ 0.08 * rwa)     → LEAN_VERIFIED

  theorem meets_minimums_sound :
    meets_basel3_minimums c t1 tot = true →
    c ≥ 0.045 ∧ t1 ≥ 0.06 ∧ tot ≥ 0.08           → LEAN_VERIFIED (decide)

TRUST: Z3_PROVEN ∧ LLM_JUDGED (regulatory alignment) = LLM_JUDGED
  To promote: have compliance officer review oracle judgments on regulatory alignment
H¹ = 0
```

---

## EXAMPLE 5: Microservice System (Python + Go + Protobuf + K8s)

### The problem
A Python ML service and a Go API gateway communicate via Protobuf.
The LLM generates the Go handler, but the Protobuf field it reads was
renamed in the latest .proto, and the timeout it sets doesn't match
the Kubernetes readiness probe configuration.

### What the developer writes

```protobuf
// proto/prediction.proto
syntax = "proto3";

message PredictionRequest {
    string model_id = 1;
    repeated float features = 2;
    int32 top_k = 3;              // was "num_results" in v1
}

message PredictionResponse {
    repeated Prediction predictions = 1;
    float latency_ms = 2;
    string model_version = 3;
}

message Prediction {
    string label = 1;
    float confidence = 2;
}
```

```python
# ml_service/predict.py
from deppy.hybrid import guarantee, check, assume

@guarantee("""
    Accepts PredictionRequest via gRPC.
    Returns PredictionResponse with len(predictions) == request.top_k.
    latency_ms is wall-clock time of inference only (not network).
    Responds within 500ms for batch size 1 (p99).
    If model_id not found, returns gRPC NOT_FOUND.
""")
async def predict(request: PredictionRequest) -> PredictionResponse:
    assume("request.features is non-empty")
    assume("request.top_k >= 1 and request.top_k <= 100")

    model = model_registry.get(request.model_id)
    if model is None:
        raise GrpcError(code=NOT_FOUND, message=f"Model {request.model_id} not found")

    start = time.monotonic()
    raw_predictions = model.predict(np.array(request.features), top_k=request.top_k)
    latency = (time.monotonic() - start) * 1000

    check("len(raw_predictions) == request.top_k")

    return PredictionResponse(
        predictions=[Prediction(label=p.label, confidence=p.score) for p in raw_predictions],
        latency_ms=latency,
        model_version=model.version,
    )
```

```go
// gateway/handlers/predict.go
// @deppy:guarantee("proxies prediction request, enforces timeout, returns JSON")
// @deppy:assume("ml_service implements predict as specified in ml_service/predict.py")

func HandlePredict(w http.ResponseWriter, r *http.Request) {
    var req PredictHTTPRequest
    json.NewDecoder(r.Body).Decode(&req)

    // @deppy:check("req.Features is non-empty")
    // @deppy:check("req.TopK >= 1 && req.TopK <= 100")

    ctx, cancel := context.WithTimeout(r.Context(), 2*time.Second)
    defer cancel()

    grpcReq := &pb.PredictionRequest{
        ModelId:  req.ModelID,
        Features: req.Features,
        TopK:     int32(req.TopK),
    }

    resp, err := predictionClient.Predict(ctx, grpcReq)
    // ... error handling and JSON response ...
}
```

```yaml
# k8s/ml-service-deployment.yaml
# @deppy:assume("ml_service responds within 500ms p99 for batch size 1")
spec:
  containers:
    - name: ml-service
      readinessProbe:
        grpc:
          port: 50051
        initialDelaySeconds: 5
        periodSeconds: 10
        timeoutSeconds: 1    # readiness probe timeout
      resources:
        limits:
          memory: "2Gi"
          nvidia.com/gpu: "1"
```

### What `deppy hybrid compile` produces

```
═══════════════════════════════════════════════════════════════
 CROSS-LANGUAGE CROSS-INFRA HYBRID TYPE ANALYSIS
 Python ↔ Go ↔ Protobuf ↔ Kubernetes
═══════════════════════════════════════════════════════════════

THEORY PACKS:
  ✓ protobuf_theory: message field tracking, type compatibility, versioning
  ✓ grpc_theory: service contracts, error codes, deadline propagation
  ✓ kubernetes_theory: probe timeouts, resource limits, container specs

PROTOBUF SCHEMA CHECK:
  ✓ Python PredictionRequest.model_id ↔ Proto field 1 (string)     ✓
  ✓ Python PredictionRequest.features ↔ Proto field 2 (repeated float) ✓
  ✓ Python PredictionRequest.top_k ↔ Proto field 3 (int32)         ✓
  ✓ Go pb.PredictionRequest.ModelId ↔ Proto field 1                 ✓
  ✓ Go pb.PredictionRequest.Features ↔ Proto field 2                ✓
  ✓ Go pb.PredictionRequest.TopK ↔ Proto field 3                    ✓
  
  ⚠ DRIFT CHECK: Proto field 3 was renamed from "num_results" to "top_k"
    If any client still uses the old name → DRIFT hallucination
    Current codebase: all references use "top_k" ✓

TIMEOUT COHERENCE (cross-infra cocycle check):
  Go gateway timeout:        2000ms (context.WithTimeout)
  Python service guarantee:  500ms p99
  K8s readiness probe:       1000ms (timeoutSeconds: 1)
  
  ✓ 500ms (service) < 1000ms (probe) < 2000ms (gateway)  — timeout chain is consistent
  ✓ Gateway timeout > service p99 — gateway won't prematurely cancel

  ⚠ WARNING: If service has a cold-start spike > 1000ms,
    readiness probe will fail → pod marked unhealthy → cascading failure
    Recommendation: initialDelaySeconds should account for model loading time

gRPC ERROR CODE COHERENCE:
  Python: raises NOT_FOUND when model_id not found
  Go: must handle NOT_FOUND from gRPC → return HTTP 404
  → Check Go error handling maps gRPC NOT_FOUND → HTTP 404  ✓

H¹(Language × Layer × Infra) = 0 — all cross-boundary contracts agree
```

---

## EXAMPLE 6: Research → Production (Jupyter Notebook → Python Package + Paper)

### The problem
A researcher writes an algorithm in a Jupyter notebook with a paper claim
"our method achieves O(n log n) time and is guaranteed to converge."
The LLM translates it to a production Python package. The production code
is O(n²) (missed the heap optimization), and the convergence claim is only
true for convex objectives (the paper's assumption) but the production
code is called on non-convex objectives.

### What the researcher writes

```python
# research/optimizer.py
from deppy.hybrid import spec, guarantee, given, hole, check, assume

given("""
    Theorem 3.2 from our paper (arXiv:2025.12345):
    For convex objectives f with L-Lipschitz gradients,
    Algorithm 1 converges to ε-optimal in O(L/ε) iterations.
    
    Theorem 3.4:
    The per-iteration cost is O(n log n) using a priority queue
    for the top-k gradient selection step.
""")

@guarantee("""
    Implements Algorithm 1 from arXiv:2025.12345.
    Time complexity: O(n log n) per iteration.
    Converges for convex L-Lipschitz objectives.
    Returns x such that f(x) - f(x*) ≤ epsilon.
""")
def sparse_gradient_descent(
    f: Callable, grad_f: Callable,
    x0: np.ndarray, epsilon: float,
    k: int, max_iter: int = 10000
) -> np.ndarray:
    assume("f is convex with L-Lipschitz gradient")
    assume("epsilon > 0")
    assume("k <= len(x0)")

    x = x0.copy()
    for t in range(max_iter):
        g = grad_f(x)

        # The key step: select top-k gradient components
        top_k_indices = hole("""
            Select the k indices with largest absolute gradient values.
            Must use a heap/partial sort for O(n log k) ⊆ O(n log n) complexity.
            Do NOT use full sort (that would be O(n log n) but with worse constants).
        """)

        sparse_grad = np.zeros_like(g)
        sparse_grad[top_k_indices] = g[top_k_indices]

        step_size = hole("compute step size using 1/(L * sqrt(t+1)) schedule")

        x = x - step_size * sparse_grad

        if np.linalg.norm(sparse_grad) < epsilon:
            break

        check("only k components of sparse_grad are nonzero")

    return x
```

### What `deppy hybrid compile` produces

```
═══════════════════════════════════════════════════════════════
 HYBRID TYPE ANALYSIS: research/optimizer.py
 PAPER GROUNDING MODE: arXiv:2025.12345
═══════════════════════════════════════════════════════════════

GIVEN (paper theorems imported):
  Theorem 3.2: convergence for convex L-Lipschitz, O(L/ε) iterations
  Theorem 3.4: O(n log n) per iteration with priority queue
  Source: arXiv:2025.12345
  Trust: HUMAN_AUTHORED (peer-reviewed paper)

  ⚠ GROUNDING CHECK:
    arXiv:2025.12345 — verified exists on arXiv  ✓
    Theorem 3.2 references checked against paper abstract  ✓ (oracle, conf 0.91)

ASSUME ANALYSIS:
  "f is convex with L-Lipschitz gradient"
    → SEMANTIC assumption — cannot be checked structurally
    → This assumption MUST be propagated to all callers
    → Any call site that passes a non-convex f violates this assumption
    → OBLIGATION: every call site must either prove convexity or explicitly assume it

HOLE 1: "Select top-k indices... must use heap for O(n log k)"
  Synthesized:
    top_k_indices = np.argpartition(np.abs(g), -k)[-k:]
  
  Structural verification:
    ✓ np.argpartition exists in NumPy API registry (numpy ≥ 1.8)  ✓
    ✓ Returns k indices  ✓ (Z3: len(result) == k)
    ✓ Indices in range [0, len(g))  ✓
  
  Complexity verification (oracle):
    ✓ np.argpartition uses introselect → O(n) average, O(n log n) worst case
    ✓ This satisfies "O(n log n)" from the paper  ✓
    ⚠ NOTE: np.argpartition is O(n) average, which is BETTER than the paper claims.
      The spec said "use a heap for O(n log k)" but argpartition is more efficient.
      This is ACCEPTABLE — the implementation meets or exceeds the spec.

HOLE 2: "step size using 1/(L * sqrt(t+1))"
  Synthesized:
    step_size = 1.0 / (L * math.sqrt(t + 1))

  ⚠ STRUCTURAL HALLUCINATION:
    Variable 'L' is not defined in scope!
    The function parameter list does not include L (Lipschitz constant).
    This is a hallucination — the LLM assumed L was available.
    
    H¹(INTENT, CODE) ≠ 0: the paper says "L-Lipschitz" but the code
    doesn't take L as a parameter.
    
    REMEDIATION: Add L as a function parameter, or estimate L from grad_f.

CROSS-REFERENCE: production call sites
  Found in production/optimize_portfolio.py:
    result = sparse_gradient_descent(portfolio_loss, portfolio_grad, x0, 1e-4, k=10)
  
  ⚠ ASSUMPTION VIOLATION:
    portfolio_loss is non-convex (it includes position limits and transaction costs)
    But sparse_gradient_descent assumes "f is convex"!
    
    H¹(CallSite × Layer) ≠ 0:
    The production code violates the paper's assumption.
    Convergence guarantee does NOT hold for this call.
    
    REMEDIATION:
    Option A: Use a non-convex variant of the algorithm
    Option B: Convexify the objective (relax position limits)
    Option C: Weaken the guarantee to "local convergence" and re-verify

TRUST REPORT:
  Paper grounding: HUMAN_AUTHORED (arXiv verified)
  Hole 1 (top-k): Z3_PROVEN (structure) ∧ LLM_JUDGED (complexity)
  Hole 2 (step size): CONTRADICTED (L not in scope)
  Convergence: CONTRADICTED (non-convex call site violates assumption)
  
  Overall: CONTRADICTED — 2 obstructions must be resolved
  H¹ = Z₂ ⊕ Z₂ (two independent generators)
```

### Why this is the holy grail

No existing tool catches the THREE bugs here:
1. **Missing parameter L** — a structural hallucination the LLM made
2. **Non-convex production usage** — a CROSS-FILE assumption violation that
   requires understanding the paper's theorems AND the call site's objective
3. **The researcher's own claim** is correctly grounded in the paper and correctly
   propagated as an assumption — so when production code violates it, the
   system traces the inconsistency back to the specific theorem and assumption

This is formal verification from idea (paper theorem) to implementation
(production code), with every step typed, every assumption tracked, every
gap measured as cohomology.

---

## SUMMARY: WHAT THE HOLY GRAIL ACTUALLY DOES

| Scenario | What LLMs get wrong | What deppy hybrid catches | How |
|----------|---------------------|--------------------------|-----|
| Data pipeline | Silent NULL handling, join cardinality, timezone mismatch | Schema disagreement Python↔SQL, row count violation | Z3 on DataFrame shapes, cross-language layer cocycle |
| ML training | Wrong tensor shapes, hallucinated API, mismatched hyperparameters | Shape errors at every operation, API existence, cross-file config | Dependent types over tensor dims, API registry, cross-file analysis |
| Web API | Wrong field names, unhandled error codes, stale contract | Frontend↔backend field mismatch, error code gaps | Cross-language presheaf, error code set comparison |
| Finance | Wrong formula version, unit confusion (bps vs %), threshold errors | Formula mismatch with regulation, unit type errors | Given (regulatory axioms), Z3 on arithmetic, unit types |
| Microservices | Proto field renames, timeout mismatches, error code mapping | Timeout chain inconsistency, proto drift, gRPC↔HTTP mapping | Cross-infra cocycle, timeout arithmetic, proto version tracking |
| Research→prod | Missing parameter, violated assumption in production, complexity claim | Unbound variable, assumption violation at call site, paper grounding | Cross-file assumption propagation, oracle on paper claims, provenance |

**In every case, the system produces:**
1. A precise obstruction (H¹ generator) saying WHAT is wrong
2. A trust level saying HOW CERTAIN we are
3. A Lean proposition (or Z3 certificate) for every structural claim
4. A remediation suggestion
5. A provenance chain tracing every claim to its origin
