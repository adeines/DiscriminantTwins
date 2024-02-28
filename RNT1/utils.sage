# Auxillary and Helper functions live here

_genus0_primes = [2, 3, 5, 7, 13]

def weierstrass_class(E):
    r"""
    Return the Weierstrass class of E.

    INPUT:

    - ``E`` -- elliptic curve over a number field

    OUTPUT: an ideal class

    Examples:

        sage: P.<x> = QQ[]
        sage: K.<a> = NumberField(x^2 - 10)
        sage: E = EllipticCurve([a, a, 0, 1263*a - 8032, 62956*a - 305877])
        sage: weierstrass_class(E)
        Fractional ideal class (2, a)
        sage: E = EllipticCurve('11a1')
        sage: weierstrass_class(E)
        NotImplementedError: Not implemented for QQ.

    """
    K = E.base_ring()
    if K == QQ:
        raise NotImplementedError('Not implemented for QQ.')
    H = K.class_group()
    D = E.discriminant()
    aDelta = K.ideal(1)
    for p, e in K.ideal(D).factor():
        pE = E.local_minimal_model(p)
        tau = pE.isomorphism_to(E)
        vp = (tau.u).valuation(p)
        aDelta *= p^(-vp)
    return(H(aDelta))

def dit_ideal_generators(K, p):
    r"""
    Returns lambda, a number field element such that for each fp dividing p,
    and for each 0 < k \leq e, fp^(12k/(p-1)) = lambda OK.

    INPUT:

    - ``K`` -- number field
    - ``p`` -- a prime from the set [2, 3, 5, 7, 13]

    OUPTUT: a list of number field elements

    EXAMPLES:

        sage: P.<x> = QQ[]
        sage: K.<a> = NumberField(x^3 - 2)
        sage: dit_ideal_generators(K, 2)
        [1, 16, 256, 4096]
        sage: dit_ideal_generators(K, 5)
        [1, -2*a^2 + 19*a + 7, 1, -3*a^2 + a - 1]
        sage: dit_ideal_generators(QQ, 3)
        [1, 729]
    """
    if p not in _genus0_primes:
        raise NotImplementedError('Only implemented for p in [2, 3, 5, 7, 13].')
    M = ZZ(12/(p-1))
    if K == QQ:
        # p factors as p and e = 1
        return [1, p^M]
    # otherwise:
    T0p = []
    pfac = K.ideal(p).factor()
    for fp, e in pfac:
        for k in range(e+1):
            fpk = fp^(k*M)
            if fpk.is_principal():
                T0p.append(fpk.gens_reduced()[0])
    return T0p

def is_singular_value(p, t0):
    r"""
    Return True or False.

    Given a prime p for which X_0(p) has genus 1, this function
    returns if t0 is a singular value for the Barrios-curve parameterization.
    This follows Lemma 3.3 from Barrios' "Explicit Classisification of Isogeny Graphs
    of Rational Elliptic Curves."

    INPUT:
    - ``p`` -- a prime from the set [2, 3, 5, 7, 13]
    - ``t0`` -- a number field element

    OUTPUT: True or False

    EXAMPLES:

        sage: is_singular_value(3, 27)
        False
        sage: is_singular_value(3, -27)
        True
        sage: P.<x> = QQ[]
        sage: K.<a> = NumberField(x^2 + 22*x + 125)
        sage: is_singular_value(5, a)
        True
    """
    if p not in _genus0_primes:
        raise NotImplementedError('Only implemented for p in [2, 3, 5, 7, 13].')
    if p == 2 and t0 == -64: return True
    elif p == 3 and t0 == -27: return True
    elif p == 5 and t0^2 + 22*t0 + 125 == 0: return True
    elif p == 7 and t0^2 + 13*t0 + 49 == 0: return True
    elif p == 13 and (t0^2 + 6*t0 + 13)*(t0^2 + 5*t0 + 13) == 0: return True
    else: return False

def discriminant_ideal_twins_special_j_invariants(K):
    r"""
    Returns a list of pairs of discriminant ideal twins,
    both with j-invariant 0 or 1728.

    INPUT:

    - ``K`` -- number field

    OUTPUT: a list of pairs of elliptic curves that are discriminant ideal twins

    EXAMPLES:

        sage: P.<x> = QQ[]
        sage: K.<a> = NumberField(x^2 + 1)
        sage: print(len(discriminant_ideal_twins_special_j_invariants(K)))
        0
        sage: K.<a> = NumberField(x^2 + 3)
        sage: print(len(discriminant_ideal_twins_special_j_invariants(K)))
        0
        sage: K.<a> = NumberField(x^2 - 2)
        sage: print(len(discriminant_ideal_twins_special_j_invariants(K)))
        1
        sage: discriminant_ideal_twins_special_j_invariants(QQ)
        []
        sage: K.<a> = NumberField(x^2 + 6)
        sage: print(len(discriminant_ideal_twins_special_j_invariants(K)))
        2

    """
    load('explicit_isogeny_models.sage')
    DiscIdealTwins = []
    if K == QQ:
        # There are none over QQ
        return []
    units = K.roots_of_unity()
    p2fac = K.ideal(2).factor()
    p3fac = K.ideal(3).factor()
    if len(units) % 6 != 0 and all([e%2 == 0 for pf, e in p3fac]):
        # Then we can have 3-isogenous DITs both with j-invs 0
        DiscIdealTwins.append([calE1_0(K(1)), calE2_0(K(1))])
    if len(units) % 4 != 0 and all([e%2 == 0 for pf, e in p2fac]):
        # Then we can have 2-isogenous DITs both with j-invs 1728
        DiscIdealTwins.append([calE1_1728(K(1)), calE2_1728(K(1))])
    return DiscIdealTwins



def discriminant_ideal_twins_nonsingular_j_invariants(K):
    r"""
    Returns a list of pairs of discriminant ideal twins, where the j-invariants
    are not both 0 or 1728.

    INPUT:

    - `K` -- number field

    OUTPUT: a list of pairs of elliptic curves that are discriminant ideal twins

    EXAMPLES:

        sage:
    """
    from itertools import product
    load('explicit_isogeny_models.sage')
    DiscIdealTwins = []
    if K == QQ:
        units = [1, -1]
    else:
        units = K.roots_of_unity()
    T0 = [dit_ideal_generators(K, p) for p in _genus0_primes]
    for p, T0p in zip(_genus0_primes, T0):
        m = 12/(p-1)
        pm = p^m
        for t, u in product(T0p, units):
            t0 = t*u
            if t0 in [pm, -pm]:
                # These are twists of t0 = 1, -1 so we can skip them
                continue
            if is_singular_value(p, t0): continue
            E1, E2 = isog_curves(p, t0, 1)
            if E1.minimal_discriminant_ideal() == E2.minimal_discriminant_ideal():
                if E1.is_isomorphic(E2) or E1.isogeny_degree(E2) == 1:
                    # I'm being a bit lazy here.  I could use the results from section 3, Theorem 3.9
                    # to preimptively remove these, or I could just check on the go.
                    continue
                else:
                    DiscIdealTwins.append([E1, E2])
            else:
                Warning = "Should have discriminant ideal twins, but don't."
                assert E1.minimal_discriminant_ideal() == E2.minimal_discriminant_ideal(), (Warning)
    return DiscIdealTwins

def discriminant_ideal_twins(K):
    r"""
    Returns a list of lists.

    Given an quadratic imaginary number field K, this returns all lists, p, t0, E1, E2,
    of elliptic curves defined over K such that E1 and E2 are p-isogenous
    discriminant ideal twins for p in the set 2, 3, 5, 7, 13 and t0 is the parameter.

    Note: the curves E1, E2 are not unique to a paraticular p, t0.

    INPUT:

    - ``K`` -- quadratic imaginary number field

    OUTPUT: a list of lists of the form [p, t0, E1, E2]

    EXAMPLES:

        sage: P.<x> = QQ[]
        sage: K.<a> = NumberField(x^2 + 22*x + 125)
        sage: DITs = discriminant_ideal_twins(K)
        sage: print(len(DITs))
        55
    """
    load('explicit_isogeny_models.sage')
    if K == QQ:
        SpecialJ = discriminant_ideal_twins_special_j_invariants(K)
        NonSingularJ = discriminant_ideal_twins_nonsingular_j_invariants(K)
        return SpecialJ + NonSingularJ
    if K.degree() != 2:
        raise ValueError("Number field must have degree 2.")
    if not K.is_totally_imaginary():
        raise ValueError("Number field must be imaginary.")
    # First, find Discriminant Ideal Twins where both have j-invariant 0 or 1728
    SpecialJ = discriminant_ideal_twins_special_j_invariants(K)
    NonSingularJ = discriminant_ideal_twins_nonsingular_j_invariants(K)
    return SpecialJ + NonSingularJ