"""Exact tools for transferring a full-circle phase cover to every large n.

No certificate is asserted merely by importing this module.  All public
interval outputs are outward rational bounds.  log_bounds uses an elementary
atanh series and a rigorous geometric remainder.
"""
from fractions import Fraction as F
from functools import lru_cache


@lru_cache(maxsize=200000)
def log_bounds(value, terms=100):
    value = F(value)
    if value <= 0:
        raise ValueError("logarithm argument must be positive")
    if value < 1:
        lo, hi = log_bounds(1 / value, terms)
        return -hi, -lo
    z = (value - 1) / (value + 1)
    total, power = F(0), z
    for j in range(terms):
        total += 2 * power / (2 * j + 1)
        power *= z * z
    return total, total + 2 * power / ((2 * terms + 1) * (1 - z * z))


def multiply_intervals(first, second):
    products = [a * b for a in first for b in second]
    return min(products), max(products)


def centered_phase_bounds(a, center, endpoint, minimum_scale, terms=100):
    """Range of M log((Mu0+center)/(Mu0+a)), over every real M>=M0."""
    a, center, endpoint, minimum_scale = map(
        F, (a, center, endpoint, minimum_scale))
    lo, hi = log_bounds(
        (minimum_scale * endpoint + center) /
        (minimum_scale * endpoint + a), terms)
    limit = (center - a) / endpoint
    return min(minimum_scale * lo, limit), max(minimum_scale * hi, limit)


def source_bounds(t_interval, endpoint, height, a_left, a_width,
                  v_left, v_width, minimum_scale, terms=100):
    """A common inner phase-image interval and outward slope enclosure.

    The returned image is in base-3 units, after the harmless rotation
    t*M*log(1+3**height/(2*M*u0))/log(3).
    A lower endpoint smaller than upper endpoint certifies that closed
    interval is contained in EVERY image for all t in t_interval, M>=M0.
    Slope bounds apply before a possible coordinate swap.
    """
    t_interval = tuple(map(F, t_interval))
    endpoint, a_left, a_width, v_left, v_width, minimum_scale = map(
        F, (endpoint, a_left, a_width, v_left, v_width, minimum_scale))
    center = F(3**height, 2)
    h_lower = centered_phase_bounds(
        a_left + a_width, center, endpoint, minimum_scale, terms)
    h_upper = centered_phase_bounds(
        a_left, center, endpoint, minimum_scale, terms)
    # sup(lower corner) and inf(upper corner), giving a common inner image.
    lower_numerator = (
        log_bounds(v_left, terms)[1]
        + multiply_intervals(t_interval, h_lower)[1])
    upper_numerator = (
        log_bounds(v_left + v_width, terms)[0]
        + multiply_intervals(t_interval, h_upper)[0])
    log3 = log_bounds(F(3), terms)
    lower = max(lower_numerator / z for z in log3)
    upper = min(upper_numerator / z for z in log3)
    slope_lower = (t_interval[0] * v_left * a_width /
                   ((endpoint + (a_left + a_width) / minimum_scale) * v_width))
    slope_upper = (t_interval[1] * (v_left + v_width) * a_width /
                   (endpoint * v_width))
    return {"image": (lower, upper), "slope": (slope_lower, slope_upper)}


def check_ternary_prefix(prefix, depth):
    if not 0 <= prefix < 3**depth:
        return False
    for _ in range(depth):
        prefix, digit = divmod(prefix, 3)
        if digit not in (0, 2):
            return False
    return prefix == 0


def cycle_edge_lower(t_interval, endpoint, minimum_scale,
                     a_current_left, a_next_right,
                     v_current_right, v_next_left, shift_difference, terms=100,
                     fixed_scale=False):
    """Uniform lower bound for the unnormalised overlap of one cycle edge.

    The current source's upper corner must exceed the next source's lower
    corner. Integer shifts are in base-3 units, so contribute shift*log(3).
    The final edge of a one-turn cycle uses next=first shifted by +1.
    """
    t_interval = tuple(map(F, t_interval))
    endpoint, minimum_scale, a_current_left, a_next_right = map(
        F, (endpoint, minimum_scale, a_current_left, a_next_right))
    at_minimum = log_bounds(
        (minimum_scale * endpoint + a_next_right) /
        (minimum_scale * endpoint + a_current_left), terms)
    at_infinity = (a_next_right - a_current_left) / endpoint
    if fixed_scale:
        scale_interval=(minimum_scale*at_minimum[0],minimum_scale*at_minimum[1])
    else:
        scale_interval = (
            min(minimum_scale * at_minimum[0], at_infinity),
            max(minimum_scale * at_minimum[1], at_infinity))
    scale_lower = multiply_intervals(t_interval, scale_interval)[0]
    log_v_lower = log_bounds(F(v_current_right) / F(v_next_left), terms)[0]
    log3 = log_bounds(F(3), terms)
    shift_lower = min(F(shift_difference) * z for z in log3)
    return log_v_lower + scale_lower + shift_lower


EXACT_BANDS = (
    (F(11, 9), F(2027, 1624)),
    (F(11, 7), F(21, 11)),
    (F(1624, 2027), F(9, 11)),
    (F(11, 21), F(7, 11)),
)
GRAPH_BANDS = (
    (F(89,73),F(171,137)), (F(101,79),F(183,143)),
    (F(89,57),F(171,89)), (F(143,61),F(237,101)),
    (F(137,57),F(219,89)),
)
ALLOWED_BANDS=set(EXACT_BANDS+GRAPH_BANDS+tuple((1/b,1/a) for a,b in GRAPH_BANDS))


def certify_cycle(cycle, prefix, t_interval, minimum_m, terms=60,
                  endpoint_depth=6,fixed_scale=False):
    """Read the floating discoverer's INTEGER source data and prove its cycle.

    No floating field in cycle is used. t_interval must supply exact rationals.
    This checks a proposed minimum_m, rather than claiming it is minimal.
    """
    assert check_ternary_prefix(prefix, endpoint_depth) and prefix > 0
    height, depth = cycle["height"], cycle["depth"]
    assert minimum_m >= endpoint_depth + height
    endpoint = F(prefix, 3**endpoint_depth)
    t_interval = tuple(map(F, t_interval))
    assert 1 <= t_interval[0] <= t_interval[1] <= 3
    minimum_scale = 3**minimum_m
    result = certify_geometry(cycle, endpoint, t_interval, minimum_scale, terms,
                              fixed_scale=fixed_scale)
    result.update(minimum_m=minimum_m, minimum_n=minimum_scale,
                  prefix=prefix, endpoint_depth=endpoint_depth,
                  t_interval=list(map(str, t_interval)))
    return result


def certify_geometry(cycle, endpoint, t_interval, minimum_scale, terms=60,
                     fixed_scale=False):
    """Exact full-circle cycle over abstract positive coefficient parameters.

    In the universal form use endpoint=1, t_interval=c_interval and
    minimum_scale=Z0. This proves all Z>=Z0, with c=t/u0 and Z=M*u0.
    """
    endpoint, minimum_scale = F(endpoint), F(minimum_scale)
    t_interval = tuple(map(F, t_interval))
    assert endpoint > 0 and minimum_scale > 0 and 0 < t_interval[0] <= t_interval[1]
    height, depth = cycle["height"], cycle["depth"]
    bands=tuple(tuple(map(F,pair)) for pair in cycle.get("exact_bands",EXACT_BANDS))
    assert all(pair in ALLOWED_BANDS for pair in bands)
    sources = []
    slope_margin = None
    for source in cycle["sources"]:
        numerator, a_depth = source["a_numerator"], source["a_depth"]
        v_numerator = source["v_numerator"]
        assert check_ternary_prefix(numerator, a_depth)
        assert check_ternary_prefix(v_numerator, depth + 1)
        assert 2 * 3**depth <= v_numerator < 3**(depth + 1)
        a_width = F(3**height, 3**a_depth)
        a_left = numerator * a_width
        v_width = F(1, 3**(depth + 1))
        v_left = v_numerator * v_width
        lower = (t_interval[0] * v_left * a_width /
                 ((endpoint + (a_left + a_width) / minimum_scale) * v_width))
        upper_endpoint=endpoint+a_left/minimum_scale if fixed_scale else endpoint
        upper = t_interval[1] * (v_left + v_width) * a_width / (upper_endpoint * v_width)
        band = bands[source["band"]]
        margin = min(lower - band[0], band[1] - upper)
        slope_margin = margin if slope_margin is None else min(slope_margin, margin)
        sources.append((a_left, a_left + a_width, v_left,
                        v_left + v_width, source["shift"]))
    edge_margin = None
    for index, current in enumerate(sources):
        following = sources[(index + 1) % len(sources)]
        next_shift = following[4] + int(index + 1 == len(sources))
        margin = cycle_edge_lower(
            t_interval, endpoint, minimum_scale, current[0], following[1],
            current[3], following[2], current[4] - next_shift, terms,
            fixed_scale=fixed_scale)
        edge_margin = margin if edge_margin is None else min(edge_margin, margin)
    return {
        "pass": slope_margin > 0 and edge_margin > 0,
        "minimum_scale": str(minimum_scale),
        "fixed_scale":fixed_scale,
        "cycle_length": len(sources),
        "slope_margin_lower": str(slope_margin),
        "edge_margin_lower_natural_log_units": str(edge_margin),
    }


if __name__ == "__main__":
    # Algebraic sanity checks only; this is not a full-circle certificate.
    for a in (F(0), F(9, 2), F(9)):
        interval = centered_phase_bounds(a, F(9, 2), F(548, 729), 3**12)
        assert interval[0] <= (F(9, 2) - a) / F(548, 729) <= interval[1]
    assert check_ternary_prefix(548, 6)
    print("Exact logarithm and monotonic-limit sanity checks passed.")
