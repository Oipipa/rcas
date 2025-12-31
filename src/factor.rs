use crate::expr::{Expr, Rational};
pub use crate::polynomial::Poly;
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorization {
    pub constant: Rational,
    pub factors: Vec<Factor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factor {
    pub poly: Poly,
    pub multiplicity: usize,
}

impl Factor {
    pub fn base_expr(&self, var: &str) -> Expr {
        self.poly.to_expr(var)
    }
}

impl Factorization {
    pub fn to_expr(&self, var: &str) -> Expr {
        if self.constant.is_zero() {
            return Expr::Constant(Rational::zero());
        }
        let mut expr = Expr::Constant(self.constant.clone());
        for factor in &self.factors {
            let base = factor.base_expr(var);
            let powered = if factor.multiplicity == 1 {
                base
            } else {
                Expr::Pow(
                    base.boxed(),
                    Expr::Constant(Rational::from_integer(BigInt::from(
                        factor.multiplicity as i64,
                    )))
                    .boxed(),
                )
            };
            expr = Expr::Mul(expr.boxed(), powered.boxed());
        }
        simplify(expr)
    }
}

pub fn factor_polynomial(expr: &Expr, var: &str) -> Option<Factorization> {
    let poly = Poly::from_expr(expr, var)?;
    if poly.is_zero() {
        return Some(Factorization {
            constant: Rational::zero(),
            factors: Vec::new(),
        });
    }

    let constant = poly.leading_coeff();
    let monic = poly.monic();
    let mut factors = Vec::new();

    let sf = square_free_parts(&monic);
    for (part, multiplicity) in sf {
        let mut stack = vec![part];
        while let Some(current) = stack.pop() {
            if current.degree() == Some(1) {
                factors.push(Factor {
                    poly: current,
                    multiplicity,
                });
                continue;
            }

            if let Some(root) = find_rational_root(&current) {
                let divider = Poly::from_expr(
                    &Expr::Sub(
                        Expr::Variable(var.to_string()).boxed(),
                        Expr::Constant(root.clone()).boxed(),
                    ),
                    var,
                )?;
                factors.push(Factor {
                    poly: divider.clone(),
                    multiplicity,
                });
                let next = current.div_exact(&divider)?;
                stack.push(next);
                continue;
            }

            if current.degree() == Some(4) {
                if let Some((a, b)) = split_quartic(&current) {
                    stack.push(a);
                    stack.push(b);
                    continue;
                }
            }

            factors.push(Factor {
                poly: current,
                multiplicity,
            });
        }
    }

    factors.sort_by(|a, b| {
        let deg_a = a.poly.degree().unwrap_or(0);
        let deg_b = b.poly.degree().unwrap_or(0);
        deg_a
            .cmp(&deg_b)
            .then_with(|| a.poly.to_expr(var).cmp(&b.poly.to_expr(var)))
    });

    Some(Factorization { constant, factors })
}

pub fn factor_polynomial_expr(expr: &Expr, var: &str) -> Option<Expr> {
    factor_polynomial(expr, var).map(|f| f.to_expr(var))
}

fn square_free_parts(poly: &Poly) -> Vec<(Poly, usize)> {
    let mut result = Vec::new();
    let mut i = 1;
    let mut g = Poly::gcd(poly, &poly.derivative());
    let mut y = poly.div_exact(&g).unwrap_or_else(Poly::zero);

    while !y.is_one() {
        let z = Poly::gcd(&y, &g);
        let factor = y.div_exact(&z).unwrap_or_else(Poly::zero);
        if !factor.is_one() {
            result.push((factor, i));
        }
        y = z.clone();
        g = g.div_exact(&z).unwrap_or_else(Poly::zero);
        i += 1;
    }

    if !g.is_one() {
        let g_sqrt = square_free_parts(&g);
        for (part, mult) in g_sqrt {
            result.push((part, mult + i - 1));
        }
    }

    result
}

fn find_rational_root(poly: &Poly) -> Option<Rational> {
    let degree = poly.degree()?;
    if degree == 0 {
        return None;
    }
    if degree == 1 {
        return poly.linear_root();
    }

    let (int_coeffs, _) = integer_coeffs(poly);
    let leading = int_coeffs.last()?.clone();
    let constant = int_coeffs.first()?.clone();

    let p_candidates = divisors(&constant);
    let q_candidates = divisors(&leading);

    let mut candidates = Vec::new();
    for p in &p_candidates {
        for q in &q_candidates {
            if q.is_zero() {
                continue;
            }
            let candidate = Rational::new(p.clone(), q.clone());
            candidates.push(candidate.clone());
            candidates.push(-candidate);
        }
    }
    candidates.sort();
    candidates.dedup();

    for candidate in candidates {
        if poly.evaluate(&candidate).is_zero() {
            return Some(candidate);
        }
    }
    None
}

fn integer_coeffs(poly: &Poly) -> (Vec<BigInt>, BigInt) {
    let mut lcm = BigInt::one();
    for (_, coeff) in poly.coeff_entries() {
        lcm = num_integer::lcm(lcm, coeff.denom().clone());
    }
    let degree = poly.degree().unwrap_or(0);
    let mut coeffs = vec![BigInt::zero(); degree + 1];
    for (exp, coeff) in poly.coeff_entries() {
        let scaled = coeff * Rational::from_integer(lcm.clone());
        coeffs[exp] = scaled.numer().clone();
    }
    (coeffs, lcm)
}

fn divisors(n: &BigInt) -> Vec<BigInt> {
    let mut result = Vec::new();
    let abs_n = n.abs();
    if abs_n.is_zero() {
        return vec![BigInt::zero()];
    }
    let mut d = BigInt::one();
    while &d * &d <= abs_n {
        if (&abs_n % &d).is_zero() {
            result.push(d.clone());
            let other = &abs_n / &d;
            if other != d {
                result.push(other);
            }
        }
        d += 1;
    }
    result.sort();
    result
}

fn rational_divisors(r: &Rational) -> Vec<Rational> {
    let p_divs = divisors(r.numer());
    let q_divs = divisors(r.denom());
    let mut result = Vec::new();
    for p in &p_divs {
        for q in &q_divs {
            if q.is_zero() {
                continue;
            }
            let frac = Rational::new(p.clone(), q.clone());
            result.push(frac.clone());
            result.push(-frac);
        }
    }
    result.sort();
    result.dedup();
    result
}

fn perfect_square_rational(r: &Rational) -> Option<Rational> {
    if r.is_negative() {
        return None;
    }
    let num_root = integer_sqrt_exact(r.numer())?;
    let den_root = integer_sqrt_exact(r.denom())?;
    Some(Rational::new(num_root, den_root))
}

fn integer_sqrt_exact(n: &BigInt) -> Option<BigInt> {
    if n.is_negative() {
        return None;
    }
    let root = n.sqrt();
    if &root * &root == *n {
        Some(root)
    } else {
        None
    }
}

fn split_quartic(poly: &Poly) -> Option<(Poly, Poly)> {
    if poly.degree()? != 4 {
        return None;
    }
    if poly.leading_coeff() != Rational::one() {
        return None;
    }

    let p3 = poly.coeff(3);
    let p2 = poly.coeff(2);
    let p1 = poly.coeff(1);
    let p0 = poly.coeff(0);

    let candidates = rational_divisors(&p0);
    for b in &candidates {
        if b.is_zero() && !p0.is_zero() {
            continue;
        }
        for d in &candidates {
            if (b * d) != p0 {
                continue;
            }
            let ac = p2.clone() - b - d;
            let discriminant =
                p3.clone() * p3.clone() - Rational::from_integer(4.into()) * ac.clone();
            if let Some(sqrt) = perfect_square_rational(&discriminant) {
                let two = Rational::from_integer(2.into());
                let a1 = (p3.clone() + sqrt.clone()) / two.clone();
                let c1 = p3.clone() - a1.clone();
                if check_quartic_match(&a1, b, &c1, d, &p1) {
                    let f1 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(a1.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(b.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    let f2 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(c1.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(d.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    return Some((f1, f2));
                }

                let a2 = (p3.clone() - sqrt.clone()) / two.clone();
                let c2 = p3.clone() - a2.clone();
                if check_quartic_match(&a2, b, &c2, d, &p1) {
                    let f1 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(a2.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(b.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    let f2 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(c2.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(d.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    return Some((f1, f2));
                }
            }
        }
    }
    None
}

fn check_quartic_match(
    a: &Rational,
    b: &Rational,
    c: &Rational,
    d: &Rational,
    target_p1: &Rational,
) -> bool {
    let lhs = a * d + b * c;
    lhs == *target_p1
}
