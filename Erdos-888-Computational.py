import math
from collections import defaultdict, Counter
from itertools import combinations, product as cart_product

def sieve_square_free(n):
    """Generate all square-free numbers up to n."""
    is_sf = [True] * (n + 1)
    for i in range(2, int(n**0.5) + 1):
        sq = i * i
        for j in range(sq, n + 1, sq):
            is_sf[j] = False
    return [x for x in range(1, n + 1) if is_sf[x]]

def square_free_kernel(m):
    """Compute the square-free kernel of m."""
    if m == 0:
        return 0
    kernel = 1
    d = 2
    temp = m
    while d * d <= temp:
        if temp % d == 0:
            kernel *= d
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        kernel *= temp
    return kernel

def core(a, b):
    """Compute core(a,b) = ab / gcd(a,b)^2."""
    g = math.gcd(a, b)
    return (a * b) // (g * g)

def is_square(n):
    """Check if n is a perfect square."""
    if n < 0:
        return False
    root = int(math.isqrt(n))
    return root * root == n

def check_admissible(A):
    """Check if set A satisfies the Erdos 888 condition."""
    A_sorted = sorted(A)
    # Check all 4-element subsets
    for quad in combinations(A_sorted, 4):
        a, b, c, d = quad
        if is_square(a * b * c * d):
            if a * d != b * c:
                return False
    # Check quadruples with repetitions: (x, x, x, y)
    for i, x in enumerate(A_sorted):
        for y in A_sorted[i+1:]:
            if is_square(x * x * x * y):
                if x * y != x * x:
                    return False
            if is_square(x * y * y * y):
                if x * y != y * y:
                    return False
    return True

def check_fixing_opportunity(n, kernel_set):
    """Check if a bad kernel quadruple can be fixed by scaling."""
    kernels = sorted(kernel_set)
    # Determine maximum valid scale for each kernel
    max_scales = []
    for k in kernels:
        s = 1
        while k * s * s <= n:
            s += 1
        max_scales.append(s - 1)
    
    # Try all valid scale combinations (excluding all-ones)
    scale_ranges = [range(1, ms + 1) for ms in max_scales]
    for scales in cart_product(*scale_ranges):
        if all(s == 1 for s in scales):
            continue  # Skip the kernel set itself
        
        A = [k * s * s for k, s in zip(kernels, scales)]
        if len(set(A)) != len(A):
            continue  # Skip if scaling creates duplicates
        
        A_sorted = sorted(A)
        prod = A_sorted[0] * A_sorted[1] * A_sorted[2] * A_sorted[3]
        
        if is_square(prod):
            if A_sorted[0] * A_sorted[3] == A_sorted[1] * A_sorted[2]:
                return True, A
    
    return False, None

def compute_f_sf(n):
    """Compute f_sf(n) via hypergraph vertex cover."""
    # Build hypergraph
    V = sieve_square_free(n)
    V_set = set(V)
    pair_groups = defaultdict(list)
    
    for i in range(len(V)):
        for j in range(i + 1, len(V)):
            k = core(V[i], V[j])
            pair_groups[k].append((V[i], V[j]))
    
    edges = []
    for k, pairs in pair_groups.items():
        if len(pairs) < 2:
            continue
        for i in range(len(pairs)):
            for j in range(i + 1, len(pairs)):
                p1, p2 = pairs[i], pairs[j]
                vertices = {p1[0], p1[1], p2[0], p2[1]}
                if len(vertices) == 4:
                    q = sorted(vertices)
                    if q[0] * q[3] != q[1] * q[2]:
                        edges.append(tuple(q))
    
    if not edges:
        return len(V), edges, set()
    
    # Compute minimum vertex cover via branch-and-bound
    deg = Counter()
    for e in edges:
        deg.update(e)
    
    min_cover = [set(V)]
    
    def backtrack(edge_idx, cover):
        if len(cover) >= len(min_cover[0]):
            return
        
        uncovered = None
        for i in range(edge_idx, len(edges)):
            if not any(v in cover for v in edges[i]):
                uncovered = edges[i]
                edge_idx = i
                break
        
        if uncovered is None:
            if len(cover) < len(min_cover[0]):
                min_cover[0] = cover.copy()
            return
        
        for v in sorted(uncovered, key=lambda x: deg[x], reverse=True):
            cover.add(v)
            backtrack(edge_idx + 1, cover)
            cover.remove(v)
    
    backtrack(0, set())
    
    f_sf = len(V) - len(min_cover[0])
    return f_sf, edges, min_cover[0]

def verify_theorem_3():
    """Verify the counterexample from Theorem 3."""
    print("=" * 60)
    print("VERIFICATION OF THEOREM 3")
    print("=" * 60)
    
    A = [3, 5, 126, 210]
    K = [square_free_kernel(x) for x in A]
    
    print(f"A = {A}")
    print(f"kappa(A) = K = {sorted(set(K))}")
    print()
    
    # Check A
    print("Checking A = {3, 5, 126, 210}:")
    prod_A = 3 * 5 * 126 * 210
    print(f"  Product: {prod_A} = {int(math.isqrt(prod_A))}^2")
    print(f"  ad = {3 * 210}, bc = {5 * 126}")
    print(f"  Admissible: {check_admissible(A)}")
    print()
    
    # Check K
    K_set = [3, 5, 14, 210]
    print("Checking K = {3, 5, 14, 210}:")
    prod_K = 3 * 5 * 14 * 210
    print(f"  Product: {prod_K} = {int(math.isqrt(prod_K))}^2")
    print(f"  ad = {3 * 210}, bc = {5 * 14}")
    print(f"  Admissible: {check_admissible(K_set)}")
    print()
    
    # Check fixing
    can_fix, fixed = check_fixing_opportunity(210, set(K_set))
    print(f"Can fix K via scaling: {can_fix}")
    if can_fix:
        print(f"Fixed set: {sorted(fixed)}")
    print("=" * 60)

def main():
    verify_theorem_3()
    print()
    
    print(f"{'n':>6} | {'Q(n)':>6} | {'f_sf(n)':>7} | {'density':>8} | {'#edges':>7} | {'fixable':>7}")
    print("-" * 65)
    
    test_values = [65, 100, 150, 200, 210, 300, 500, 750, 1000]
    
    for n in test_values:
        f_sf, edges, cover = compute_f_sf(n)
        Q_n = len(sieve_square_free(n))
        density = f_sf / n
        
        # Check for fixable edges
        fixable = False
        for edge in edges[:100]:  # Check first 100 edges
            can_fix, _ = check_fixing_opportunity(n, set(edge))
            if can_fix:
                fixable = True
                break
        
        print(f"{n:>6} | {Q_n:>6} | {f_sf:>7} | {density:>8.4f} | {len(edges):>7} | {str(fixable):>7}")

if __name__ == "__main__":
    main()
  
