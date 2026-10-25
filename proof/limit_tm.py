"""Convergence of the t-series (the limit in Theorem A) in the t-cutoff, bump exp(-1/(1-(y-9)^2)) on [8, 10]."""
import sys, numpy as np
sys.argv = [sys.argv[0]]
import thmA_numeric as T
for TM in (300, 600, 1000, 2000, 3000, 4000):
    print(f"t <= {TM}: limit = {T.limit(TM):+.10f}", flush=True)
