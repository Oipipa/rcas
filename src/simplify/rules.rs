use std::collections::HashMap;

use crate::core::expr::{Expr, Rational, one, zero};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

const DISTRIBUTE_TERM_LIMIT: usize = 64;

#[derive(Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
struct CanonKey(Vec<Expr>);

pub fn simplify(expr: Expr) -> Expr {
    let mut cache = HashMap::new();
    simplify_cached(expr, &mut cache)
}

fn simplify_cached(expr: Expr, cache: &mut HashMap<Expr, Expr>) -> Expr {
    if let Some(hit) = cache.get(&expr) {
        return hit.clone();
    }

    let key = expr.clone();
    let result = match expr {
        Expr::Add(a, b) => simplify_add(simplify_cached(*a, cache), simplify_cached(*b, cache)),
        Expr::Sub(a, b) => simplify_sub(simplify_cached(*a, cache), simplify_cached(*b, cache)),
        Expr::Mul(a, b) => simplify_mul(simplify_cached(*a, cache), simplify_cached(*b, cache)),
        Expr::Div(a, b) => simplify_div(simplify_cached(*a, cache), simplify_cached(*b, cache)),
        Expr::Pow(a, b) => simplify_pow(simplify_cached(*a, cache), simplify_cached(*b, cache)),
        Expr::Neg(a) => simplify_neg(simplify_cached(*a, cache)),

        Expr::Sin(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Sin(inner.boxed())),
            x => Expr::Sin(x.boxed()),
        },

        Expr::Cos(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => one(),
            Expr::Neg(inner) => Expr::Cos(inner.boxed()),
            x => Expr::Cos(x.boxed()),
        },

        Expr::Tan(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            x => Expr::Tan(x.boxed()),
        },

        Expr::Sec(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => one(),
            Expr::Neg(inner) => Expr::Sec(inner.boxed()),
            x => Expr::Sec(x.boxed()),
        },

        Expr::Csc(a) => match simplify_cached(*a, cache) {
            Expr::Neg(inner) => simplify_neg(Expr::Csc(inner.boxed())),
            x => Expr::Csc(x.boxed()),
        },

        Expr::Cot(a) => match simplify_cached(*a, cache) {
            Expr::Neg(inner) => simplify_neg(Expr::Cot(inner.boxed())),
            x => Expr::Cot(x.boxed()),
        },

        Expr::Atan(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Atan(inner.boxed())),
            x => Expr::Atan(x.boxed()),
        },

        Expr::Asin(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Asin(inner.boxed())),
            x => Expr::Asin(x.boxed()),
        },

        Expr::Acos(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => Expr::Acos(zero().boxed()),
            Expr::Neg(inner) => Expr::Acos(inner.boxed()),
            x => Expr::Acos(x.boxed()),
        },

        Expr::Asec(a) => Expr::Asec(simplify_cached(*a, cache).boxed()),
        Expr::Acsc(a) => Expr::Acsc(simplify_cached(*a, cache).boxed()),
        Expr::Acot(a) => match simplify_cached(*a, cache) {
            Expr::Neg(inner) => simplify_neg(Expr::Acot(inner.boxed())),
            x => Expr::Acot(x.boxed()),
        },

        Expr::Sinh(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Sinh(inner.boxed())),
            x => Expr::Sinh(x.boxed()),
        },

        Expr::Cosh(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => one(),
            Expr::Neg(inner) => Expr::Cosh(inner.boxed()),
            x => Expr::Cosh(x.boxed()),
        },

        Expr::Tanh(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Tanh(inner.boxed())),
            x => Expr::Tanh(x.boxed()),
        },

        Expr::Asinh(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Asinh(inner.boxed())),
            x => Expr::Asinh(x.boxed()),
        },

        Expr::Acosh(a) => Expr::Acosh(simplify_cached(*a, cache).boxed()),

        Expr::Atanh(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => zero(),
            Expr::Neg(inner) => simplify_neg(Expr::Atanh(inner.boxed())),
            x => Expr::Atanh(x.boxed()),
        },

        Expr::Exp(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => one(),
            Expr::Log(inner) => *inner,
            x => Expr::Exp(x.boxed()),
        },

        Expr::Log(a) => match simplify_cached(*a, cache) {
            x if is_one(&x) => zero(),
            Expr::Exp(inner) => *inner,
            x => Expr::Log(x.boxed()),
        },

        Expr::Abs(a) => match simplify_cached(*a, cache) {
            Expr::Constant(c) => Expr::Constant(c.abs()),
            Expr::Neg(inner) => Expr::Abs(inner.boxed()),
            Expr::Abs(inner) => Expr::Abs(inner.boxed()),
            Expr::Exp(inner) => Expr::Exp(inner.boxed()),
            x => Expr::Abs(x.boxed()),
        },

        e => e,
    };

    let result = simplify_imaginary_quadratic(result);
    cache.insert(key, result.clone());
    result
}

/// Apply simplification passes until the expression stops changing or we hit the iteration cap.
pub fn simplify_fully(expr: Expr) -> Expr {
    simplify_with_limit(expr, 64)
}

/// Apply simplification passes up to `max_iters`, returning the last value if convergence is not reached.
pub fn simplify_with_limit(expr: Expr, max_iters: usize) -> Expr {
    let mut cache = HashMap::new();
    let mut current = expr;
    for _ in 0..max_iters {
        let next = simplify_trig_once(&simplify_cached(current.clone(), &mut cache), &mut cache);
        if next == current {
            return current;
        }
        current = next;
    }
    current
}

pub fn simplify_add(x: Expr, y: Expr) -> Expr {
    rebuild_sum(collect_sum(
        flatten_sum(&x)
            .into_iter()
            .chain(flatten_sum(&y).into_iter()),
    ))
}

pub fn simplify_sub(x: Expr, y: Expr) -> Expr {
    simplify_add(x, simplify_neg(y))
}

fn flatten_sum(expr: &Expr) -> Vec<Expr> {
    match expr {
        Expr::Add(a, b) => {
            let mut out = flatten_sum(a);
            out.extend(flatten_sum(b));
            out
        }
        Expr::Sub(a, b) => {
            let mut out = flatten_sum(a);
            out.extend(flatten_sum(b).into_iter().map(simplify_neg));
            out
        }
        Expr::Neg(a) => flatten_sum(a).into_iter().map(simplify_neg).collect(),
        other => vec![other.clone()],
    }
}

fn count_sum_terms(expr: &Expr) -> usize {
    match expr {
        Expr::Add(a, b) | Expr::Sub(a, b) => count_sum_terms(a) + count_sum_terms(b),
        Expr::Neg(inner) => count_sum_terms(inner),
        _ => 1,
    }
}

fn is_zero_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(r) if r.is_zero())
}

fn is_one_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(r) if r.is_one())
}

fn is_neg_one_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Constant(r) => *r == -Rational::one(),
        Expr::Neg(inner) => is_one_expr(inner),
        _ => false,
    }
}

fn is_const_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Variable(_) => false,
        Expr::Constant(_) => true,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => is_const_expr(a) && is_const_expr(b),
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Sec(inner)
        | Expr::Csc(inner)
        | Expr::Cot(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Asec(inner)
        | Expr::Acsc(inner)
        | Expr::Acot(inner)
        | Expr::Sinh(inner)
        | Expr::Cosh(inner)
        | Expr::Tanh(inner)
        | Expr::Asinh(inner)
        | Expr::Acosh(inner)
        | Expr::Atanh(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => is_const_expr(inner),
    }
}

fn coeff_add(a: Expr, b: Expr) -> Expr {
    if is_zero_expr(&a) {
        return b;
    }
    if is_zero_expr(&b) {
        return a;
    }
    match (&a, &b) {
        (Expr::Constant(ca), Expr::Constant(cb)) => Expr::Constant(ca + cb),
        _ if a == b => Expr::Mul(
            Expr::Constant(Rational::from_integer(2.into())).boxed(),
            a.boxed(),
        ),
        _ => Expr::Add(a.boxed(), b.boxed()),
    }
}

fn coeff_mul(a: Expr, b: Expr) -> Expr {
    if is_zero_expr(&a) || is_zero_expr(&b) {
        return zero();
    }
    if is_one_expr(&a) {
        return b;
    }
    if is_one_expr(&b) {
        return a;
    }
    if is_neg_one_expr(&a) {
        return simplify_neg(b);
    }
    if is_neg_one_expr(&b) {
        return simplify_neg(a);
    }
    match (&a, &b) {
        (Expr::Constant(_), Expr::Div(num, den))
            if is_const_expr(num) && is_const_expr(den) =>
        {
            let new_num = coeff_mul(a.clone(), (**num).clone());
            return coeff_div(new_num, (**den).clone());
        }
        (Expr::Div(num, den), Expr::Constant(_))
            if is_const_expr(num) && is_const_expr(den) =>
        {
            let new_num = coeff_mul((**num).clone(), b.clone());
            return coeff_div(new_num, (**den).clone());
        }
        (Expr::Constant(ca), Expr::Constant(cb)) => Expr::Constant(ca * cb),
        _ => Expr::Mul(a.boxed(), b.boxed()),
    }
}

fn coeff_div(a: Expr, b: Expr) -> Expr {
    if is_zero_expr(&a) {
        return zero();
    }
    if is_one_expr(&b) {
        return a;
    }
    if a == b {
        return one();
    }
    match (&a, &b) {
        (Expr::Constant(ca), Expr::Constant(cb)) => {
            if cb.is_zero() {
                Expr::Div(a.boxed(), b.boxed())
            } else {
                Expr::Constant(ca / cb)
            }
        }
        (Expr::Constant(ca), _) if ca.is_negative() => {
            let pos = Expr::Constant(-ca.clone());
            simplify_neg(coeff_div(pos, b.clone()))
        }
        (Expr::Neg(inner), _) => simplify_neg(coeff_div((**inner).clone(), b.clone())),
        _ if is_neg_one_expr(&b) => simplify_neg(a),
        _ => Expr::Div(a.boxed(), b.boxed()),
    }
}

fn split_coeff(expr: &Expr) -> (Expr, Expr) {
    match expr {
        Expr::Constant(_) => (expr.clone(), one()),
        Expr::Neg(e) => {
            let (c, b) = split_coeff(e);
            (simplify_neg(c), b)
        }
        Expr::Mul(a, b) => {
            let (ca, ba) = split_coeff(a);
            let (cb, bb) = split_coeff(b);
            (coeff_mul(ca, cb), mul_norm(ba, bb))
        }
        other if is_const_expr(other) => (other.clone(), one()),
        other => (one(), other.clone()),
    }
}

fn canonical_factors(expr: &Expr) -> Vec<Expr> {
    let mut factors = flatten_mul(expr);
    factors.sort();
    factors
}

fn mul_from_sorted_factors(factors: &[Expr]) -> Expr {
    if factors.is_empty() {
        return one();
    }
    let mut iter = factors.iter().cloned();
    let first = iter.next().unwrap();
    iter.fold(first, |acc, item| Expr::Mul(acc.boxed(), item.boxed()))
}

fn mul_norm(a: Expr, b: Expr) -> Expr {
    mk_mul_list(
        factors(&a)
            .into_iter()
            .chain(factors(&b).into_iter())
            .collect(),
    )
}

fn factors(expr: &Expr) -> Vec<Expr> {
    match expr {
        Expr::Mul(a, b) => {
            let mut out = factors(a);
            out.extend(factors(b));
            out
        }
        t if is_one(t) => vec![],
        t => vec![t.clone()],
    }
}

fn collect_sum<I>(terms: I) -> HashMap<CanonKey, Expr>
where
    I: IntoIterator<Item = Expr>,
{
    let mut map = HashMap::new();
    for term in terms {
        let (c, b) = split_coeff(&term);
        if is_zero_expr(&c) {
            continue;
        }
        let factors = canonical_factors(&b);
        map.entry(CanonKey(factors))
            .and_modify(|acc: &mut Expr| *acc = coeff_add(acc.clone(), c.clone()))
            .or_insert(c);
    }
    map
}

fn flatten_mul(expr: &Expr) -> Vec<Expr> {
    match expr {
        Expr::Mul(a, b) => {
            let mut out = flatten_mul(a);
            out.extend(flatten_mul(b));
            out
        }
        t if is_one(t) => vec![],
        t => vec![t.clone()],
    }
}

fn rebuild_sum(map: HashMap<CanonKey, Expr>) -> Expr {
    let mut map = map;
    let const_term = map
        .remove(&CanonKey(Vec::new()))
        .unwrap_or_else(zero);
    let mut items: Vec<(CanonKey, Expr)> = map.into_iter().collect();
    items.sort_by(|(a, _), (b, _)| a.cmp(b));

    let mut terms: Vec<Expr> = items
        .into_iter()
        .filter_map(|(CanonKey(factors), coef)| {
            if is_zero_expr(&coef) {
                None
            } else {
                Some(term_from(&coef, mul_from_sorted_factors(&factors)))
            }
        })
        .collect();

    if !is_zero_expr(&const_term) {
        terms.push(const_term);
    }

    match terms.len() {
        0 => zero(),
        1 => terms.remove(0),
        _ => mk_add_list(terms),
    }
}

fn term_from(coef: &Expr, base: Expr) -> Expr {
    if is_zero_expr(coef) {
        return zero();
    }

    if is_one(&base) {
        return coef.clone();
    }

    if is_one_expr(coef) {
        return base;
    }

    if is_neg_one_expr(coef) {
        return simplify_neg(base);
    }

    Expr::Mul(coef.clone().boxed(), base.boxed())
}

pub fn simplify_mul(x: Expr, y: Expr) -> Expr {
    match (x, y) {
        (Expr::Add(a, b), t) => {
            let term_count = (count_sum_terms(&a) + count_sum_terms(&b)) * count_sum_terms(&t);
            if term_count <= DISTRIBUTE_TERM_LIMIT {
                simplify_add(simplify_mul(*a, t.clone()), simplify_mul(*b, t))
            } else {
                Expr::Mul(Expr::Add(a, b).boxed(), t.boxed())
            }
        }
        (Expr::Sub(a, b), t) => {
            let term_count = (count_sum_terms(&a) + count_sum_terms(&b)) * count_sum_terms(&t);
            if term_count <= DISTRIBUTE_TERM_LIMIT {
                simplify_sub(simplify_mul(*a, t.clone()), simplify_mul(*b, t))
            } else {
                Expr::Mul(Expr::Sub(a, b).boxed(), t.boxed())
            }
        }
        (t, Expr::Add(a, b)) => {
            let term_count = count_sum_terms(&t) * (count_sum_terms(&a) + count_sum_terms(&b));
            if term_count <= DISTRIBUTE_TERM_LIMIT {
                simplify_add(simplify_mul(t.clone(), *a), simplify_mul(t, *b))
            } else {
                Expr::Mul(t.boxed(), Expr::Add(a, b).boxed())
            }
        }
        (t, Expr::Sub(a, b)) => {
            let term_count = count_sum_terms(&t) * (count_sum_terms(&a) + count_sum_terms(&b));
            if term_count <= DISTRIBUTE_TERM_LIMIT {
                simplify_sub(simplify_mul(t.clone(), *a), simplify_mul(t, *b))
            } else {
                Expr::Mul(t.boxed(), Expr::Sub(a, b).boxed())
            }
        }
        (Expr::Constant(xc), Expr::Constant(yc)) => Expr::Constant(xc * yc),
        (x, y) if is_zero(&x) || is_zero(&y) => zero(),
        (x, y) if is_one(&x) => y,
        (x, y) if is_one(&y) => x,
        (x, y) => {
            let (c, b) = split_coeff(&Expr::Mul(x.boxed(), y.boxed()));
            if is_zero_expr(&c) {
                zero()
            } else {
                match b {
                    t if is_one(&t) => c,
                    _ if is_one_expr(&c) => b,
                    _ if is_neg_one_expr(&c) => simplify_neg(b),
                    _ => Expr::Mul(c.boxed(), b.boxed()),
                }
            }
        }
    }
}

pub fn simplify_div(x: Expr, y: Expr) -> Expr {
    match (x, y) {
        (Expr::Constant(n), Expr::Constant(d)) => {
            if d.is_zero() {
                Expr::Div(Expr::Constant(n).boxed(), Expr::Constant(d).boxed())
            } else {
                Expr::Constant(n / d)
            }
        }
        (x, y) if is_zero(&x) => zero(),
        (x, y) if is_one(&y) => x,
        (x, y) => {
            let (cx, bx) = split_coeff(&x);
            let (cy, by) = split_coeff(&y);
            if is_zero_expr(&cy) {
                return Expr::Div(x.boxed(), y.boxed());
            }
            let c = coeff_div(cx, cy);
            if bx == by && !is_one(&bx) {
                if is_one_expr(&c) {
                    one()
                } else {
                    c
                }
            } else {
                let core = if is_one(&by) {
                    bx
                } else {
                    Expr::Div(bx.boxed(), by.boxed())
                };
                if is_one_expr(&c) {
                    core
                } else {
                    simplify_mul(c, core)
                }
            }
        }
    }
}

pub fn simplify_pow(x: Expr, y: Expr) -> Expr {
    match (x, y) {
        (_, Expr::Constant(e)) if e.is_zero() => one(),
        (base, Expr::Constant(e)) if e.is_one() => base,
        (Expr::Constant(b), Expr::Constant(e)) => {
            if b.is_one() {
                return one();
            }
            if e.is_integer() {
                let k: BigInt = e.to_integer();
                if let Some(power) = k.abs().to_u32() {
                    if k >= BigInt::zero() {
                        let num = b.numer().pow(power);
                        let den = b.denom().pow(power);
                        return Expr::Constant(Rational::new(num, den));
                    } else if b.is_zero() {
                        return Expr::Pow(Expr::Constant(b).boxed(), Expr::Constant(e).boxed());
                    } else {
                        let num = b.denom().pow(power);
                        let den = b.numer().pow(power);
                        return Expr::Constant(Rational::new(num, den));
                    }
                }
            }
            Expr::Pow(Expr::Constant(b).boxed(), Expr::Constant(e).boxed())
        }
        (x, e @ Expr::Constant(_)) => {
            if let Expr::Constant(ref k) = e {
                if k.is_integer() {
                    let n = k.to_integer();
                    if n.is_zero() {
                        return one();
                    }
                    if n.is_one() {
                        return x;
                    }
                }
            }
            Expr::Pow(x.boxed(), e.boxed())
        }
        (x, y) => Expr::Pow(x.boxed(), y.boxed()),
    }
}

pub fn simplify_neg(expr: Expr) -> Expr {
    match expr {
        Expr::Constant(x) => Expr::Constant(-x),
        Expr::Neg(x) => *x,
        Expr::Add(a, b) => simplify_add(simplify_neg(*a), simplify_neg(*b)),
        Expr::Sub(a, b) => simplify_sub(*b, *a),
        other => Expr::Neg(other.boxed()),
    }
}

fn is_zero(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(r) if r.is_zero())
}

fn is_one(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(r) if r.is_one())
}

#[derive(Clone)]
struct TermMeta {
    coeff: Expr,
    sines: Vec<Expr>,
    coses: Vec<Expr>,
    others: Vec<Expr>,
}

fn partition_trig(factors: &[Expr]) -> (Vec<Expr>, Vec<Expr>, Vec<Expr>) {
    let mut sines = Vec::new();
    let mut coses = Vec::new();
    let mut others = Vec::new();
    for f in factors {
        match f {
            Expr::Sin(arg) => sines.push(*arg.clone()),
            Expr::Cos(arg) => coses.push(*arg.clone()),
            _ => others.push(f.clone()),
        }
    }
    (sines, coses, others)
}

fn term_meta(expr: &Expr) -> TermMeta {
    let (coeff, core) = split_coeff(expr);
    let factors = factors(&core);
    let (mut sines, mut coses, mut others) = partition_trig(&factors);
    sines.sort();
    coses.sort();
    others.sort();

    TermMeta {
        coeff,
        sines,
        coses,
        others,
    }
}

fn coeff_is_neg_of(lhs: &Expr, rhs: &Expr) -> bool {
    simplify_neg(rhs.clone()) == *lhs
}

fn combine_trig_pair(terms: &[Expr]) -> Option<(Expr, (usize, usize))> {
    let metas: Vec<TermMeta> = terms.iter().map(term_meta).collect();
    let mut buckets: HashMap<CanonKey, Vec<(usize, TermMeta)>> = HashMap::new();

    for (idx, meta) in metas.into_iter().enumerate() {
        buckets
            .entry(CanonKey(meta.others.clone()))
            .or_default()
            .push((idx, meta));
    }

    for entries in buckets.values() {
        for a in 0..entries.len() {
            for b in (a + 1)..entries.len() {
                let (idx_a, meta_a) = &entries[a];
                let (idx_b, meta_b) = &entries[b];
                if let Some(term) = try_trig_pair(meta_a, meta_b) {
                    return Some((term, (*idx_a, *idx_b)));
                }
                if let Some(term) = try_trig_pair(meta_b, meta_a) {
                    return Some((term, (*idx_a, *idx_b)));
                }
            }
        }
    }

    None
}

fn try_trig_pair(lhs: &TermMeta, rhs: &TermMeta) -> Option<Expr> {
    // Case A: sin(u)sin(v) + cos(u)cos(v) => cos(u - v)
    if lhs.sines.len() == 2
        && lhs.coses.is_empty()
        && rhs.sines.is_empty()
        && rhs.coses.len() == 2
        && lhs.coeff == rhs.coeff
        && lhs.sines == rhs.coses
    {
        let core = mul_from_sorted_factors(&lhs.others);
        let term = Expr::Cos(
            Expr::Sub(lhs.sines[0].clone().boxed(), lhs.sines[1].clone().boxed()).boxed(),
        );
        return Some(term_from(&lhs.coeff, attach_core(core, term)));
    }

    // Case B: cos(a)*k + sin(a)*(-k) => sin(sin_arg - cos_arg)
    if lhs.sines.is_empty()
        && lhs.coses.len() == 1
        && rhs.sines.len() == 1
        && rhs.coses.len() == 1
        && coeff_is_neg_of(&lhs.coeff, &rhs.coeff)
        && lhs.coses[0] == rhs.coses[0]
    {
        let core = mul_from_sorted_factors(&lhs.others);
        let term = Expr::Sin(
            Expr::Sub(rhs.sines[0].clone().boxed(), lhs.coses[0].clone().boxed()).boxed(),
        );
        return Some(term_from(&lhs.coeff, attach_core(core, term)));
    }

    // Case C: sin(a)cos(b) with matching partner and opposite coefficients.
    if lhs.sines.len() == 1
        && lhs.coses.len() == 1
        && rhs.sines.len() == 1
        && rhs.coses.len() == 1
        && coeff_is_neg_of(&lhs.coeff, &rhs.coeff)
        && lhs.sines[0] == rhs.sines[0]
        && lhs.coses[0] == rhs.coses[0]
    {
        let core = mul_from_sorted_factors(&lhs.others);
        let term = Expr::Sin(
            Expr::Sub(lhs.sines[0].clone().boxed(), lhs.coses[0].clone().boxed()).boxed(),
        );
        return Some(term_from(&lhs.coeff, attach_core(core, term)));
    }

    None
}

fn attach_core(core: Expr, trig_term: Expr) -> Expr {
    if is_one(&core) {
        trig_term
    } else {
        Expr::Mul(core.boxed(), trig_term.boxed())
    }
}

fn simplify_trig_once(expr: &Expr, cache: &mut HashMap<Expr, Expr>) -> Expr {
    let terms = flatten_sum(expr);
    if let Some((new_term, (i, j))) = combine_trig_pair(&terms) {
        let rest: Vec<Expr> = terms
            .into_iter()
            .enumerate()
            .filter_map(|(idx, t)| if idx == i || idx == j { None } else { Some(t) })
            .collect();
        simplify_cached(
            mk_add_list(
                std::iter::once(new_term)
                    .chain(rest.into_iter())
                    .collect::<Vec<_>>(),
            ),
            cache,
        )
    } else {
        expr.clone()
    }
}

fn mk_add_list(items: Vec<Expr>) -> Expr {
    if items.is_empty() {
        return zero();
    }
    let mut iter = items.into_iter();
    let first = iter.next().unwrap();
    iter.fold(first, |acc, item| Expr::Add(acc.boxed(), item.boxed()))
}

fn mk_mul_list(mut items: Vec<Expr>) -> Expr {
    items.retain(|e| !is_one(e));
    if items.is_empty() {
        return one();
    }
    items.sort();
    let mut iter = items.into_iter();
    let first = iter.next().unwrap();
    iter.fold(first, |acc, item| Expr::Mul(acc.boxed(), item.boxed()))
}

fn simplify_imaginary_quadratic(expr: Expr) -> Expr {
    let (mut coeff, base) = split_coeff(&expr);
    let mut factors = factors(&base);
    let mut changed = false;

    if let Some((idx_sqrt, sqrt_base, d)) = find_sqrt_u2_plus_d(&factors) {
        if d.is_negative() {
            let sqrt_factor = factors[idx_sqrt].clone();
            if take_neg_one_pow_neg_half(&mut coeff, &mut factors) {
                if let Some(idx) = factors.iter().position(|f| *f == sqrt_factor) {
                    factors.swap_remove(idx);
                }
                let neg_base = simplify_neg(sqrt_base);
                let new_sqrt = simplify_pow(
                    neg_base,
                    Expr::Constant(Rational::new(1.into(), 2.into())),
                );
                factors.push(new_sqrt);
                coeff = simplify_neg(coeff);
                changed = true;
            }
        }
    }

    if let Some((idx_log, u_expr, d)) = find_log_abs_u_plus_sqrt(&factors) {
        if d.is_negative() {
            let log_factor = factors[idx_log].clone();
            if take_neg_one_pow_neg_half(&mut coeff, &mut factors) {
                if let Some(idx) = factors.iter().position(|f| *f == log_factor) {
                    factors.swap_remove(idx);
                }
                let denom = simplify_pow(
                    Expr::Constant(-d.clone()),
                    Expr::Constant(Rational::new(1.into(), 2.into())),
                );
                let acos_arg = simplify_div(u_expr, denom);
                factors.push(Expr::Acos(acos_arg.boxed()));
                coeff = simplify_neg(coeff);
                changed = true;
            }
        }
    }

    if !changed {
        return expr;
    }

    let core = mk_mul_list(factors);
    term_from(&coeff, core)
}

fn take_neg_one_pow_neg_half(coeff: &mut Expr, factors: &mut Vec<Expr>) -> bool {
    if let Some(idx) = factors.iter().position(is_neg_one_pow_neg_half) {
        factors.swap_remove(idx);
        return true;
    }
    if let Some(new_coeff) = remove_factor_from_coeff(coeff, is_neg_one_pow_neg_half) {
        *coeff = new_coeff;
        return true;
    }
    false
}

fn remove_factor_from_coeff(expr: &Expr, pred: fn(&Expr) -> bool) -> Option<Expr> {
    if pred(expr) {
        return Some(one());
    }
    match expr {
        Expr::Mul(a, b) => {
            if let Some(new_a) = remove_factor_from_coeff(a, pred) {
                return Some(coeff_mul(new_a, (**b).clone()));
            }
            if let Some(new_b) = remove_factor_from_coeff(b, pred) {
                return Some(coeff_mul((**a).clone(), new_b));
            }
            None
        }
        Expr::Neg(inner) => {
            remove_factor_from_coeff(inner, pred).map(|res| simplify_neg(res))
        }
        _ => None,
    }
}

fn is_neg_one_pow_neg_half(expr: &Expr) -> bool {
    match expr {
        Expr::Pow(base, exp) => match (&**base, &**exp) {
            (Expr::Constant(b), Expr::Constant(e)) => {
                *b == -Rational::one() && *e == Rational::new((-1).into(), 2.into())
            }
            _ => false,
        },
        _ => false,
    }
}

fn find_sqrt_u2_plus_d(factors: &[Expr]) -> Option<(usize, Expr, Rational)> {
    for (idx, factor) in factors.iter().enumerate() {
        let Expr::Pow(base, exp) = factor else { continue };
        let Expr::Constant(exp) = &**exp else { continue };
        if *exp != Rational::new(1.into(), 2.into()) {
            continue;
        }
        if let Some((_u_expr, d)) = match_u2_plus_d(base) {
            return Some((idx, base.as_ref().clone(), d));
        }
    }
    None
}

fn find_log_abs_u_plus_sqrt(factors: &[Expr]) -> Option<(usize, Expr, Rational)> {
    for (idx, factor) in factors.iter().enumerate() {
        let Expr::Log(inner) = factor else { continue };
        let Expr::Abs(abs_inner) = &**inner else { continue };
        let terms = flatten_sum(abs_inner);
        if terms.len() < 2 {
            continue;
        }
        for (sqrt_idx, sqrt_term) in terms.iter().enumerate() {
            let Expr::Pow(base, exp) = sqrt_term else { continue };
            let Expr::Constant(exp) = &**exp else { continue };
            if *exp != Rational::new(1.into(), 2.into()) {
                continue;
            }
            let Some((u_expr, d)) = match_u2_plus_d(base) else { continue };

            let mut rest_terms = terms.clone();
            rest_terms.swap_remove(sqrt_idx);
            let u_candidate = rebuild_sum_from_terms(&rest_terms);
            if simplify(u_candidate.clone()) == simplify(u_expr.clone()) {
                return Some((idx, u_candidate, d));
            }
        }
    }
    None
}

fn rebuild_sum_from_terms(terms: &[Expr]) -> Expr {
    rebuild_sum(collect_sum(terms.iter().cloned()))
}

fn match_u2_plus_d(expr: &Expr) -> Option<(Expr, Rational)> {
    let terms = flatten_sum(expr);
    if terms.len() != 2 {
        return None;
    }
    let mut u_expr = None;
    let mut d_val = None;
    for term in terms {
        match term {
            Expr::Pow(base, exp) => {
                if let Expr::Constant(ref k) = *exp {
                    if k.is_integer() && k.to_integer() == BigInt::from(2) {
                        u_expr = Some(*base.clone());
                    }
                }
            }
            Expr::Constant(c) => d_val = Some(c),
            _ => {}
        }
    }
    Some((u_expr?, d_val?))
}
