"""Reproduce the optional numerical diagnostics in the manuscript.

These calculations are sanity checks, not proof inputs.  The script uses
NumPy for exhaustive finite-cube enumeration and stable elementary formulas
for the channel-dependent scalar margins.
"""

import math
from decimal import Decimal, getcontext

import numpy as np


RHO_GRID = (0.10, 0.25, 0.50, 0.75, 0.90, 0.99)
L = math.log(2.0)
getcontext().prec = 70
D = Decimal
D_ONE = D(1)
D_TWO = D(2)
D_L = D_TWO.ln()
D_PI = D(
    "3.141592653589793238462643383279502884197169399375105820974944592307816"
)


def entropy_of_mean(value):
    """Binary entropy in nats for a sign with the given mean."""
    value = np.asarray(value, dtype=float)
    plus = (1.0 + value) / 2.0
    minus = (1.0 - value) / 2.0
    result = np.zeros_like(value)
    mask = plus > 0.0
    result[mask] -= plus[mask] * np.log(plus[mask])
    mask = minus > 0.0
    result[mask] -= minus[mask] * np.log(minus[mask])
    return result


def cube_points(dimension):
    ids = np.arange(1 << dimension, dtype=np.uint32)
    return 2 * ((ids[:, None] >> np.arange(dimension)) & 1).astype(np.int8) - 1


def noise_matrix(points, rho):
    products = points[:, None, :] * points[None, :, :]
    return np.prod((1.0 + rho * products) / 2.0, axis=2)


def all_boolean_functions(dimension):
    size = 1 << dimension
    ids = np.arange(1 << size, dtype=np.uint32)[:, None]
    return 2 * ((ids >> np.arange(size, dtype=np.uint32)) & 1).astype(np.int8) - 1


def monotone_functions(dimension):
    """Generate monotone truth tables by pairing lower and upper sections."""
    functions = np.array([[-1], [1]], dtype=np.int8)
    for _ in range(dimension):
        pairs = []
        for lower in functions:
            allowed = np.all(lower[None, :] <= functions, axis=1)
            for upper in functions[allowed]:
                pairs.append(np.concatenate((lower, upper)))
        functions = np.asarray(pairs, dtype=np.int8)
    return functions


def finite_cube_row(functions, points, rho, monotone=False):
    # Sum the small cube explicitly; this also avoids BLAS-specific
    # floating-point warnings observed for the equivalent matrix product.
    posterior = np.einsum(
        "fx,yx->fy", functions, noise_matrix(points, rho), optimize=False
    )
    means = functions.mean(axis=1)
    information = entropy_of_mean(means) - entropy_of_mean(posterior).mean(axis=1)
    dictator = L - float(entropy_of_mean(rho))
    leads = information - dictator

    excluded = np.zeros(len(functions), dtype=bool)
    for coordinate in range(points.shape[1]):
        excluded |= np.all(functions == points[:, coordinate], axis=1)
        if not monotone:
            excluded |= np.all(functions == -points[:, coordinate], axis=1)
    runner_up = np.max(leads[~excluded])
    return float(np.max(leads)), float(-runner_up)


def low_diagnostics():
    def h(value):
        return float(entropy_of_mean(value))

    def g(value):
        return math.atanh(value)

    def tangent_data(t):
        coefficient = math.log(2.0 / (1.0 + t)) / (1.0 - t) ** 2
        contact = 2.0 * t - g(t) / coefficient
        return coefficient, contact

    a0, z0 = tangent_data(2.0 / 5.0)
    a1, z1 = tangent_data(2.0 / 3.0)
    beta = (1.0 / a0 - 1.0 / a1) / (z1 - z0)
    alpha = 1.0 / a0 + beta * z0
    energy_cap = (7.0 / 8.0) ** 2
    r0 = 5.0 / 8.0
    r1 = math.tanh(31.0 / 20.0)

    def coefficient(r):
        return 1.0 / (alpha - beta * r * r)

    def b0(r):
        return (1.0 - r) * (1.0 + r - energy_cap * r * r) - (
            alpha - beta * r * r
        ) * h(r)

    def b0_prime(r):
        return (
            -2.0 * (1.0 + energy_cap) * r
            + 3.0 * energy_cap * r * r
            + (alpha - beta * r * r) * g(r)
            + 2.0 * beta * r * h(r)
        )

    def b0_second(r):
        return (
            -2.0 * (1.0 + energy_cap)
            + 6.0 * energy_cap * r
            + (alpha - beta * r * r) / (1.0 - r * r)
            - 4.0 * beta * r * g(r)
            + 2.0 * beta * h(r)
        )

    def b0_third(r):
        return (
            6.0 * energy_cap
            - 6.0 * beta * g(r)
            - 6.0 * beta * r / (1.0 - r * r)
            + 2.0 * r * (alpha - beta * r * r) / (1.0 - r * r) ** 2
        )

    local = (1.0 - r1 * r1) * h(5.0 * r1 / 8.0) - (
        1.0 - 5.0 * r1 * r1 / 8.0
    ) * h(r1)
    slack = (
        coefficient(r0)
        * (1.0 - r0)
        * (1.0 + r0 - energy_cap * r0 * r0)
        + r0 * r0 / 2.0
        - L
    )
    return alpha, beta, (
        local,
        b0_prime(r0),
        b0_second(r0),
        b0_third(r0),
        b0_second(4.0 / 5.0),
        b0_second(r1),
        b0(r1),
        slack,
    )


def channel(height):
    """Stable channel data even when tanh(height) rounds to one."""
    x = math.exp(-height)
    q = x * x
    correlation = (1.0 - q) / (1.0 + q)
    entropy = math.log1p(q) + 2.0 * height * q / (1.0 + q)
    angle = math.pi / 2.0 - 2.0 * math.atan(x)
    return x, correlation, entropy, angle


def profile_f(height):
    _, correlation, entropy, _ = channel(height)
    return entropy / correlation


def angle_profile(height):
    _, correlation, _, angle = channel(height)
    return angle * angle / correlation


def correction_profile(height):
    return height - angle_profile(height)


def middle_diagnostics(height):
    _, correlation, _, angle = channel(height)
    slope = angle / correlation
    alpha = (angle + math.sinh(height)) / height
    penalty = slope * alpha
    eta = angle * angle * penalty / (penalty + 1.0)
    beta = 2.0 * correlation / eta
    half = height / 2.0
    profile = math.log(
        half * profile_f(half) / (height * profile_f(height))
    ) - beta * (correction_profile(height) - correction_profile(half))
    energy = (
        angle * angle
        - correlation * correction_profile(height)
        - eta / 2.0
    )
    mean = (
        penalty
        - 2.0 * angle * angle / math.sinh(height) ** 2
        - slope / alpha
        - correlation * height
    )
    return profile, energy, mean


def middle_profile_margin(height, relative_height):
    _, correlation, _, angle = channel(height)
    slope = angle / correlation
    alpha = (angle + math.sinh(height)) / height
    penalty = slope * alpha
    eta = angle * angle * penalty / (penalty + 1.0)
    beta = 2.0 * correlation / eta
    comparison_height = relative_height * height
    return math.log(
        comparison_height
        * profile_f(comparison_height)
        / (height * profile_f(height))
    ) - beta * (
        correction_profile(height) - correction_profile(comparison_height)
    )


def middle_mesh_summary():
    minimum_profile = math.inf
    minimum_energy = math.inf
    minimum_mean = math.inf
    for height in np.linspace(1.55, 3.5, 196):
        _, energy, mean = middle_diagnostics(float(height))
        minimum_energy = min(minimum_energy, energy)
        minimum_mean = min(minimum_mean, mean)
        for relative_height in np.linspace(0.01, 0.99, 99):
            minimum_profile = min(
                minimum_profile,
                middle_profile_margin(float(height), float(relative_height)),
            )
    return minimum_profile, minimum_energy, minimum_mean


def decimal_atan_small(value):
    """Arctangent series; tail diagnostics use value <= exp(-7/2)."""
    term = value
    total = value
    index = 1
    while True:
        term *= -(value * value)
        updated = total + term / D(2 * index + 1)
        if updated == total:
            return total
        total = updated
        index += 1


def decimal_channel(height):
    x = (-height).exp()
    q = x * x
    correlation = (D_ONE - q) / (D_ONE + q)
    entropy = (D_ONE + q).ln() + D_TWO * height * q / (D_ONE + q)
    angle = D_PI / D_TWO - D_TWO * decimal_atan_small(x)
    return x, correlation, entropy, angle


def decimal_profile_f(height):
    _, correlation, entropy, _ = decimal_channel(height)
    return entropy / correlation


def decimal_angle_profile(height):
    _, correlation, _, angle = decimal_channel(height)
    return angle * angle / correlation


def tail_diagnostics(height):
    height = D(str(height))
    x, correlation, entropy, angle = decimal_channel(height)
    slope = angle / correlation
    alpha = (angle + (D_ONE / x - x) / D_TWO) / height
    penalty = slope * alpha
    degree = height / D_TWO + D(5) / D(4)

    def weight(spectral_degree):
        return penalty * spectral_degree / (penalty + spectral_degree)

    d1 = (weight(degree) - weight(D_ONE)) * correlation**2
    d2 = (weight(degree) - weight(D_TWO)) * correlation**4
    db = d1 - d2 / D_TWO
    multiplier = (slope + D_ONE / alpha) ** 2
    b = slope * slope * (D_TWO + D_ONE / penalty)
    cd = multiplier * weight(degree) - b
    baseline = D_TWO * angle * angle + cd * (D_L - entropy) / D_L

    half = height / D_TWO
    k_lsi = (
        penalty
        * penalty
        * (D_TWO * degree - D(3)).exp()
        / (D_TWO * (penalty + degree) * (penalty + D_ONE))
    )
    small = (
        baseline / height
        - correlation
        - multiplier
        * k_lsi
        * correlation**2
        * decimal_profile_f(height)
        / (half * decimal_profile_f(half))
    )
    join_ratio = decimal_profile_f(height) / decimal_profile_f(half)
    join = (
        baseline * half / height
        - correlation * decimal_angle_profile(half)
        - multiplier * (d2 / D_TWO + db * join_ratio)
    )

    cutoff = D_ONE / (D_ONE + (D(8) / D(3)) * x)
    target = decimal_profile_f(height) / cutoff
    lower, upper = D(0), height
    for _ in range(250):
        midpoint = (lower + upper) / D_TWO
        if decimal_profile_f(midpoint) > target:
            lower = midpoint
        else:
            upper = midpoint
    retained_height = (lower + upper) / D_TWO
    cutoff_margin = (
        baseline * retained_height / height
        - correlation * decimal_angle_profile(retained_height)
        - multiplier * (d2 / D_TWO + db * cutoff)
    )
    return small, join / x.sqrt(), cutoff_margin / x


def tail_diagnostics_float(height):
    """Fast double-precision version used only for the sign mesh."""
    x, correlation, entropy, angle = channel(height)
    slope = angle / correlation
    alpha = (angle + math.sinh(height)) / height
    penalty = slope * alpha
    degree = height / 2.0 + 5.0 / 4.0

    def weight(spectral_degree):
        return penalty * spectral_degree / (penalty + spectral_degree)

    d1 = (weight(degree) - weight(1.0)) * correlation**2
    d2 = (weight(degree) - weight(2.0)) * correlation**4
    db = d1 - d2 / 2.0
    multiplier = (slope + 1.0 / alpha) ** 2
    b = slope * slope * (2.0 + 1.0 / penalty)
    cd = multiplier * weight(degree) - b
    baseline = 2.0 * angle * angle + cd * (L - entropy) / L
    half = height / 2.0
    k_lsi = (
        penalty
        * penalty
        * math.exp(2.0 * degree - 3.0)
        / (2.0 * (penalty + degree) * (penalty + 1.0))
    )
    small = (
        baseline / height
        - correlation
        - multiplier
        * k_lsi
        * correlation**2
        * profile_f(height)
        / (half * profile_f(half))
    )
    join_ratio = profile_f(height) / profile_f(half)
    join = (
        baseline * half / height
        - correlation * angle_profile(half)
        - multiplier * (d2 / 2.0 + db * join_ratio)
    )
    cutoff = 1.0 / (1.0 + (8.0 / 3.0) * x)
    target = profile_f(height) / cutoff
    lower, upper = 0.0, height
    for _ in range(100):
        midpoint = (lower + upper) / 2.0
        if profile_f(midpoint) > target:
            lower = midpoint
        else:
            upper = midpoint
    retained_height = (lower + upper) / 2.0
    cutoff_margin = (
        baseline * retained_height / height
        - correlation * angle_profile(retained_height)
        - multiplier * (d2 / 2.0 + db * cutoff)
    )
    return small, join / math.sqrt(x), cutoff_margin / x


def tail_mesh_summary():
    minima = [math.inf, math.inf, math.inf]
    for height in np.linspace(3.5, 20.0, 1651):
        for index, value in enumerate(tail_diagnostics_float(float(height))):
            minima[index] = min(minima[index], value)
    return tuple(minima)


def main():
    points4 = cube_points(4)
    all4 = all_boolean_functions(4)
    points5 = cube_points(5)
    monotone5 = monotone_functions(5)

    print("finite cube: rho, maximum lead n=4, n=4 runner-up deficit, n=5 monotone runner-up deficit")
    for rho in RHO_GRID:
        maximum4, deficit4 = finite_cube_row(all4, points4, rho)
        _, deficit5 = finite_cube_row(monotone5, points5, rho, monotone=True)
        print(f"{rho:.2f} {maximum4:.12g} {deficit4:.12g} {deficit5:.12g}")

    alpha, beta, low = low_diagnostics()
    print(f"low coefficients: alpha={alpha:.15g} beta={beta:.15g}")
    print("low margins:", " ".join(f"{value:.12g}" for value in low))

    print("middle: ell, half-profile reserve, energy reserve, mean reserve")
    for height in (1.55, 2.0, 2.5, 3.0, 3.5):
        values = middle_diagnostics(height)
        print(f"{height:g}", " ".join(f"{value:.12g}" for value in values))
    print(
        "middle mesh minima:",
        " ".join(f"{value:.12g}" for value in middle_mesh_summary()),
    )

    print("tail: ell, M_small, exp(ell/2) M_join, exp(ell) M_cut")
    for height in (3.5, 5.0, 10.0, 20.0):
        values = tail_diagnostics(height)
        print(f"{height:g}", " ".join(f"{value:.12g}" for value in values))
    print(
        "tail mesh minima:",
        " ".join(f"{value:.12g}" for value in tail_mesh_summary()),
    )


if __name__ == "__main__":
    main()
