#!/usr/bin/env sage

# Target: find E/F_{q'} with #E = p where p = Fq(BLS12-381)
p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

print(f"Target order p = {p}")
print(f"p is prime: {is_prime(p)}")
print(f"p bit length: {p.nbits()}")

# Search: for small traces t, compute q' = p + t - 1, check if q' is prime,
# then check if a simple curve y^2 = x^3 + b over F_{q'} has order p.
#
# #E(F_{q'}) = q' + 1 - trace => q' = p + trace - 1
#
# We try both positive and negative traces starting from small |t|.
# For each prime q', we try y^2 = x^3 + b for small b.

import sys

found = False
curves_checked = 0

for t in range(2, 10000):
    for sign in [1, -1]:
        trace = sign * t
        q_prime = p + trace - 1
        if q_prime < 2:
            continue
        if not is_prime(q_prime):
            continue

        print(f"  Trying trace={trace}, q' is prime, checking curves...", flush=True)

        F = GF(q_prime)
        # Try y^2 = x^3 + b (a=0) for small b
        for b in range(1, 100):
            try:
                E = EllipticCurve(F, [0, b])
                curves_checked += 1
                order = E.order()
                if order == p:
                    print(f"\n{'='*60}")
                    print(f"FOUND!")
                    print(f"{'='*60}")
                    print(f"  trace t = {trace}")
                    print(f"  q' = {q_prime}")
                    print(f"  q' hex = {hex(q_prime)}")
                    print(f"  q' bit length = {q_prime.nbits()}")
                    print(f"  curve: y^2 = x^3 + {b} over F_{{q'}}")
                    print(f"  #E = {order}")
                    print(f"  #E == p: {order == p}")

                    # Find a generator (since order is prime, any non-identity point generates)
                    G = E.random_point()
                    while G == E(0):
                        G = E.random_point()

                    print(f"  Generator G:")
                    print(f"    x = {hex(int(G[0]))}")
                    print(f"    y = {hex(int(G[1]))}")

                    # Verify order
                    assert p * G == E(0), "Order check failed!"
                    assert (p - 1) * G != E(0), "Order too small!"
                    print(f"  Order verification: PASSED")

                    # Security checks
                    print(f"\n  Security checks:")
                    print(f"  q' != p (not anomalous): {q_prime != p}")
                    emb_deg = None
                    for k in range(1, 101):
                        if pow(int(q_prime), k, int(p)) == 1:
                            emb_deg = k
                            print(f"    Embedding degree k = {k}")
                            break
                    if emb_deg is None:
                        print(f"    No small embedding degree (checked k=1..100): GOOD")

                    disc = trace * trace - 4 * q_prime
                    print(f"  CM discriminant D = {disc}")

                    print(f"\n  Curves checked total: {curves_checked}")
                    found = True
                    break
                else:
                    # Print progress occasionally
                    if curves_checked % 5 == 0:
                        print(f"    b={b}: order mismatch (curves checked: {curves_checked})", flush=True)
            except Exception as e:
                continue
        if found:
            break
    if found:
        break

if not found:
    print(f"\nNo curve found with y^2 = x^3 + b. Curves checked: {curves_checked}")
    print("Trying y^2 = x^3 + ax + b ...")
    for t in range(2, 1000):
        for sign in [1, -1]:
            trace = sign * t
            q_prime = p + trace - 1
            if q_prime < 2 or not is_prime(q_prime):
                continue
            print(f"  Trying trace={trace}, q' is prime, checking curves...", flush=True)
            F = GF(q_prime)
            for a in range(1, 20):
                for b in range(1, 20):
                    try:
                        E = EllipticCurve(F, [a, b])
                        curves_checked += 1
                        if E.order() == p:
                            print(f"\n{'='*60}")
                            print(f"FOUND!")
                            print(f"{'='*60}")
                            print(f"  trace t = {trace}")
                            print(f"  q' = {hex(q_prime)}")
                            print(f"  curve: y^2 = x^3 + {a}x + {b} over F_{{q'}}")
                            G = E.random_point()
                            while G == E(0):
                                G = E.random_point()
                            print(f"  Generator G:")
                            print(f"    x = {hex(int(G[0]))}")
                            print(f"    y = {hex(int(G[1]))}")
                            assert p * G == E(0)
                            assert (p - 1) * G != E(0)
                            print(f"  Order verified!")
                            print(f"  q' != p: {q_prime != p}")
                            found = True
                            break
                    except:
                        continue
                if found:
                    break
            if found:
                break
        if found:
            break

if not found:
    print(f"\nNo curve found in search range. Total curves checked: {curves_checked}")
