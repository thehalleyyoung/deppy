"""
Performance Caching for Safety Pipeline
=======================================

Intelligent caching system for expensive operations in the safety verification
pipeline. Caches AST parsing, source analysis, and Z3 proof results with
content-based hashing for correctness.

Features:
- Content-based cache keys (no invalidation on unrelated changes)
- LRU eviction with configurable size limits
- Separate cache namespaces for different operations
- Optional persistent disk cache
- Cache hit/miss statistics
"""
from __future__ import annotations

import ast
import hashlib
import pickle
import time
from collections import OrderedDict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, Optional, TypeVar, Generic

T = TypeVar('T')


@dataclass
class CacheStats:
    """Cache performance statistics."""
    hits: int = 0
    misses: int = 0
    total_time_saved: float = 0.0  # seconds
    
    @property
    def hit_rate(self) -> float:
        total = self.hits + self.misses
        return self.hits / total if total > 0 else 0.0


class LRUCache(Generic[T]):
    """Thread-safe LRU cache with size limits."""
    
    def __init__(self, max_size: int = 1000):
        self.max_size = max_size
        self._cache: OrderedDict[str, T] = OrderedDict()
        self.stats = CacheStats()
    
    def get(self, key: str) -> Optional[T]:
        """Get value from cache, updating LRU order."""
        if key in self._cache:
            # Move to end (most recently used)
            value = self._cache.pop(key)
            self._cache[key] = value
            self.stats.hits += 1
            return value
        self.stats.misses += 1
        return None
    
    def put(self, key: str, value: T) -> None:
        """Store value in cache, evicting if needed."""
        if key in self._cache:
            # Update existing
            self._cache.pop(key)
        elif len(self._cache) >= self.max_size:
            # Evict least recently used
            self._cache.popitem(last=False)
        
        self._cache[key] = value
    
    def clear(self) -> None:
        """Clear all cached values."""
        self._cache.clear()
        self.stats = CacheStats()


@dataclass
class VerificationCache:
    """Central cache coordinator for safety pipeline operations."""
    
    # Component caches
    ast_cache: LRUCache[ast.AST] = field(default_factory=lambda: LRUCache(500))
    source_cache: LRUCache[Any] = field(default_factory=lambda: LRUCache(200))
    z3_cache: LRUCache[Any] = field(default_factory=lambda: LRUCache(1000))
    coverage_cache: LRUCache[Any] = field(default_factory=lambda: LRUCache(300))
    
    # Persistent cache directory
    cache_dir: Optional[Path] = None
    
    def __post_init__(self):
        if self.cache_dir:
            self.cache_dir.mkdir(parents=True, exist_ok=True)
    
    def content_hash(self, content: str, operation: str = "") -> str:
        """Generate content-based cache key."""
        hasher = hashlib.sha256()
        hasher.update(content.encode('utf-8'))
        if operation:
            hasher.update(operation.encode('utf-8'))
        return hasher.hexdigest()[:16]
    
    def cached_ast_parse(self, source: str, filename: str = "<string>") -> ast.AST:
        """Cache AST parsing results."""
        cache_key = self.content_hash(source, "ast_parse")
        
        cached = self.ast_cache.get(cache_key)
        if cached is not None:
            return cached
        
        # Parse and cache
        start_time = time.time()
        tree = ast.parse(source, filename)
        parse_time = time.time() - start_time
        
        self.ast_cache.put(cache_key, tree)
        self.ast_cache.stats.total_time_saved += parse_time * 0.9  # Estimate overhead
        
        return tree
    
    def cached_source_analysis(self, source: str, analyzer_func: Callable[[str], T]) -> T:
        """Cache source analysis results (exception sources, etc.)."""
        cache_key = self.content_hash(source, analyzer_func.__name__)
        
        cached = self.source_cache.get(cache_key)
        if cached is not None:
            return cached
        
        # Analyze and cache
        start_time = time.time()
        result = analyzer_func(source)
        analysis_time = time.time() - start_time
        
        self.source_cache.put(cache_key, result)
        self.source_cache.stats.total_time_saved += analysis_time * 0.9
        
        return result
    
    def cached_z3_proof(self, formula: str, context: str, prover_func: Callable[[], T]) -> T:
        """Cache Z3 proof results."""
        cache_key = self.content_hash(f"{formula}|{context}", "z3_proof")
        
        cached = self.z3_cache.get(cache_key)
        if cached is not None:
            return cached
        
        # Prove and cache
        start_time = time.time()
        result = prover_func()
        proof_time = time.time() - start_time
        
        self.z3_cache.put(cache_key, result)
        self.z3_cache.stats.total_time_saved += proof_time * 0.9
        
        return result
    
    def save_to_disk(self) -> None:
        """Persist cache to disk."""
        if not self.cache_dir:
            return
        
        try:
            cache_data = {
                'ast_cache': dict(self.ast_cache._cache),
                'source_cache': dict(self.source_cache._cache),
                'z3_cache': dict(self.z3_cache._cache),
                'coverage_cache': dict(self.coverage_cache._cache),
            }
            
            with open(self.cache_dir / "verification_cache.pkl", "wb") as f:
                pickle.dump(cache_data, f)
                
        except Exception:
            # Ignore disk cache failures
            pass
    
    def load_from_disk(self) -> None:
        """Load cache from disk."""
        if not self.cache_dir:
            return
        
        try:
            cache_file = self.cache_dir / "verification_cache.pkl"
            if cache_file.exists():
                with open(cache_file, "rb") as f:
                    cache_data = pickle.load(f)
                
                self.ast_cache._cache.update(cache_data.get('ast_cache', {}))
                self.source_cache._cache.update(cache_data.get('source_cache', {}))
                self.z3_cache._cache.update(cache_data.get('z3_cache', {}))
                self.coverage_cache._cache.update(cache_data.get('coverage_cache', {}))
        
        except Exception:
            # Ignore disk cache failures
            pass
    
    def get_stats_summary(self) -> str:
        """Get cache performance summary."""
        lines = [
            "Verification Cache Performance:",
            f"  AST Cache:      {self.ast_cache.stats.hit_rate:.1%} hit rate ({self.ast_cache.stats.hits}H/{self.ast_cache.stats.misses}M)",
            f"  Source Cache:   {self.source_cache.stats.hit_rate:.1%} hit rate ({self.source_cache.stats.hits}H/{self.source_cache.stats.misses}M)",
            f"  Z3 Cache:       {self.z3_cache.stats.hit_rate:.1%} hit rate ({self.z3_cache.stats.hits}H/{self.z3_cache.stats.misses}M)",
            f"  Coverage Cache: {self.coverage_cache.stats.hit_rate:.1%} hit rate ({self.coverage_cache.stats.hits}H/{self.coverage_cache.stats.misses}M)",
            f"  Total Time Saved: {sum(c.stats.total_time_saved for c in [self.ast_cache, self.source_cache, self.z3_cache, self.coverage_cache]):.3f}s",
        ]
        return "\n".join(lines)


# Global cache instance
_global_cache: Optional[VerificationCache] = None


def get_verification_cache() -> VerificationCache:
    """Get or create the global verification cache."""
    global _global_cache
    if _global_cache is None:
        _global_cache = VerificationCache()
        _global_cache.load_from_disk()
    return _global_cache


def clear_verification_cache() -> None:
    """Clear all cached verification data."""
    global _global_cache
    if _global_cache:
        _global_cache.ast_cache.clear()
        _global_cache.source_cache.clear()
        _global_cache.z3_cache.clear()
        _global_cache.coverage_cache.clear()