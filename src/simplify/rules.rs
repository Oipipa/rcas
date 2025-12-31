use std::collections::HashMap;

use crate::expr::{Expr, Rational, one, zero};
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

        Expr::Exp(a) => match simplify_cached(*a, cache) {
            x if is_zero(&x) => one(),
            x => Expr::Exp(x.boxed()),
        },

        Expr::Log(a) => match simplify_cached(*a, cache) {
            x if is_one(&x) => zero(),
            x => Expr::Log(x.boxed()),
        },

        Expr::Abs(a) => match simplify_cached(*a, cache) {
            Expr::Constant(c) => Expr::Constant(c.abs()),
            Expr::Neg(inner) => Expr::Abs(inner.boxed()),
            x => Expr::Abs(x.boxed()),
        },

        e => e,
    };

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

fn split_coeff(expr: &Expr) -> (Rational, Expr) {
    match expr {
        Expr::Constant(c) => (c.clone(), one()),
        Expr::Neg(e) => {
            let (c, b) = split_coeff(e);
            (-c, b)
        }
        Expr::Mul(a, b) => {
            let (ca, ba) = split_coeff(a);
            let (cb, bb) = split_coeff(b);
            (ca * cb, mul_norm(ba, bb))
        }
        other => (Rational::one(), other.clone()),
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

fn collect_sum<I>(terms: I) -> HashMap<CanonKey, Rational>
where
    I: IntoIterator<Item = Expr>,
{
    let mut map = HashMap::new();
    for term in terms {
        let (c, b) = split_coeff(&term);
        if c.is_zero() {
            continue;
        }
        let factors = canonical_factors(&b);
        map.entry(CanonKey(factors))
            .and_modify(|acc| *acc += &c)
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

fn rebuild_sum(map: HashMap<CanonKey, Rational>) -> Expr {
    let mut map = map;
    let const_term = map
        .remove(&CanonKey(Vec::new()))
        .unwrap_or_else(Rational::zero);
    let mut items: Vec<(CanonKey, Rational)> = map.into_iter().collect();
    items.sort_by(|(a, _), (b, _)| a.cmp(b));

    let mut terms: Vec<Expr> = items
        .into_iter()
        .filter_map(|(CanonKey(factors), coef)| {
            if coef.is_zero() {
                None
            } else {
                Some(term_from(&coef, mul_from_sorted_factors(&factors)))
            }
        })
        .collect();

    if !const_term.is_zero() {
        terms.push(Expr::Constant(const_term));
    }

    match terms.len() {
        0 => zero(),
        1 => terms.remove(0),
        _ => mk_add_list(terms),
    }
}

fn term_from(coef: &Rational, base: Expr) -> Expr {
    if coef.is_zero() {
        return zero();
    }

    if is_one(&base) {
        return Expr::Constant(coef.clone());
    }

    if coef.is_one() {
        return base;
    }

    if coef == &-Rational::one() {
        return simplify_neg(base);
    }

    Expr::Mul(Expr::Constant(coef.clone()).boxed(), base.boxed())
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
            if c.is_zero() {
                zero()
            } else {
                match b {
                    t if is_one(&t) => Expr::Constant(c),
                    _ if c.is_one() => b,
                    _ if c == -Rational::one() => simplify_neg(b),
                    _ => Expr::Mul(Expr::Constant(c).boxed(), b.boxed()),
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
            let c = cx / cy;
            if bx == by && !is_one(&bx) {
                if c.is_one() { one() } else { Expr::Constant(c) }
            } else {
                let core = if is_one(&by) {
                    bx
                } else {
                    Expr::Div(bx.boxed(), by.boxed())
                };
                match c.cmp(&Rational::one()) {
                    std::cmp::Ordering::Equal => core,
                    _ => simplify_mul(Expr::Constant(c), core),
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
    coeff: Rational,
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
        && lhs.coeff == -rhs.coeff.clone()
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
        && lhs.coeff == -rhs.coeff.clone()
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
