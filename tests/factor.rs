use num_traits::Zero;
use rcas::{Poly, Rational, factor_polynomial, parse_expr, simplify_fully};

fn rational_const(num: i64) -> Rational {
    Rational::from_integer(num.into())
}

fn assert_factorization(input: &str, constant: Rational, expected: &[(&str, usize)]) {
    let expr = simplify_fully(parse_expr(input).expect("parse input"));
    let factorization = factor_polynomial(&expr, "x").expect("factorization");
    assert_eq!(
        factorization.constant, constant,
        "leading constant for {input}"
    );

    let mut expected_factors: Vec<(Poly, usize)> = expected
        .iter()
        .map(|(txt, mult)| {
            let parsed = parse_expr(txt).expect("parse factor");
            let poly = Poly::from_expr(&parsed, "x").expect("factor parse to poly");
            (poly, *mult)
        })
        .collect();
    expected_factors.sort_by(|(p1, m1), (p2, m2)| {
        p1.degree()
            .cmp(&p2.degree())
            .then_with(|| p1.to_expr("x").cmp(&p2.to_expr("x")))
            .then_with(|| m1.cmp(m2))
    });

    let mut actual: Vec<(Poly, usize)> = factorization
        .factors
        .iter()
        .map(|f| (f.poly.clone(), f.multiplicity))
        .collect();
    actual.sort_by(|(p1, m1), (p2, m2)| {
        p1.degree()
            .cmp(&p2.degree())
            .then_with(|| p1.to_expr("x").cmp(&p2.to_expr("x")))
            .then_with(|| m1.cmp(m2))
    });

    assert_eq!(actual, expected_factors, "factors for {input}");

    let rebuilt = factorization.to_expr("x");
    let rebuilt_poly = Poly::from_expr(&rebuilt, "x").expect("rebuilt poly");
    let original_poly = Poly::from_expr(&expr, "x").expect("original poly");
    assert_eq!(
        rebuilt_poly, original_poly,
        "factorization should reconstruct {input}"
    );
}

#[test]
fn trivial_factorizations() {
    let cases: Vec<(&str, Rational, Vec<(&str, usize)>)> = vec![
        (
            "x^2 - 1",
            rational_const(1),
            vec![("x - 1", 1), ("x + 1", 1)],
        ),
        ("x^2 + 2*x + 1", rational_const(1), vec![("x + 1", 2)]),
        ("x^2 - 3*x", rational_const(1), vec![("x", 1), ("x - 3", 1)]),
        (
            "x^3 - x",
            rational_const(1),
            vec![("x", 1), ("x - 1", 1), ("x + 1", 1)],
        ),
        ("2*x^2", rational_const(2), vec![("x", 2)]),
        ("3*x^3", rational_const(3), vec![("x", 3)]),
        ("x", rational_const(1), vec![("x", 1)]),
        ("5", rational_const(5), vec![]),
        ("0", Rational::zero(), vec![]),
        (
            "x^3 + x^2 - x - 1",
            rational_const(1),
            vec![("x + 1", 2), ("x - 1", 1)],
        ),
        (
            "x^3 - 4*x^2 + 4*x",
            rational_const(1),
            vec![("x", 1), ("x - 2", 2)],
        ),
        (
            "x^4 - x^2",
            rational_const(1),
            vec![("x", 2), ("x - 1", 1), ("x + 1", 1)],
        ),
        (
            "x^2 - 4",
            rational_const(1),
            vec![("x - 2", 1), ("x + 2", 1)],
        ),
        ("x^2 + x", rational_const(1), vec![("x", 1), ("x + 1", 1)]),
        (
            "x^3 + 2*x^2 + x",
            rational_const(1),
            vec![("x", 1), ("x + 1", 2)],
        ),
        ("4*x^2 + 4*x + 1", rational_const(4), vec![("x + 1/2", 2)]),
        (
            "x^3 - 8",
            rational_const(1),
            vec![("x - 2", 1), ("x^2 + 2*x + 4", 1)],
        ),
        (
            "x^3 + 8",
            rational_const(1),
            vec![("x + 2", 1), ("x^2 - 2*x + 4", 1)],
        ),
        (
            "x^4 - 16",
            rational_const(1),
            vec![("x - 2", 1), ("x + 2", 1), ("x^2 + 4", 1)],
        ),
        ("x^4 + 4*x^2 + 4", rational_const(1), vec![("x^2 + 2", 2)]),
        (
            "x^3 - 9*x",
            rational_const(1),
            vec![("x", 1), ("x - 3", 1), ("x + 3", 1)],
        ),
        (
            "2*x^2 + 4*x",
            rational_const(2),
            vec![("x", 1), ("x + 2", 1)],
        ),
        (
            "x^2 - x - 6",
            rational_const(1),
            vec![("x - 3", 1), ("x + 2", 1)],
        ),
        (
            "3*x^2 - 12",
            rational_const(3),
            vec![("x - 2", 1), ("x + 2", 1)],
        ),
        (
            "x^3 - 2*x^2 - x + 2",
            rational_const(1),
            vec![("x - 1", 1), ("x + 1", 1), ("x - 2", 1)],
        ),
    ];

    assert_eq!(cases.len(), 25);
    for (input, constant, factors) in cases {
        assert_factorization(input, constant, &factors);
    }
}

#[test]
fn nontrivial_factorizations() {
    let cases: Vec<(&str, Rational, Vec<(&str, usize)>)> = vec![
        (
            "x^4 - 1",
            rational_const(1),
            vec![("x - 1", 1), ("x + 1", 1), ("x^2 + 1", 1)],
        ),
        (
            "x^4 - 5*x^2 + 4",
            rational_const(1),
            vec![("x - 2", 1), ("x + 2", 1), ("x - 1", 1), ("x + 1", 1)],
        ),
        (
            "x^3 - 6*x^2 + 11*x - 6",
            rational_const(1),
            vec![("x - 1", 1), ("x - 2", 1), ("x - 3", 1)],
        ),
        (
            "x^3 + 3*x^2 + 3*x + 1",
            rational_const(1),
            vec![("x + 1", 3)],
        ),
        (
            "2*x^3 + 3*x^2 - 8*x - 12",
            rational_const(2),
            vec![("x - 2", 1), ("x + 2", 1), ("x + 3/2", 1)],
        ),
        (
            "x^5 - 3*x^4 + 3*x^3 - x^2",
            rational_const(1),
            vec![("x", 2), ("x - 1", 3)],
        ),
        (
            "x^6 - 1",
            rational_const(1),
            vec![
                ("x - 1", 1),
                ("x + 1", 1),
                ("x^2 + x + 1", 1),
                ("x^2 - x + 1", 1),
            ],
        ),
        (
            "x^4 + 4*x^3 + 6*x^2 + 4*x + 1",
            rational_const(1),
            vec![("x + 1", 4)],
        ),
        (
            "4*x^3 + 4*x^2 - 12*x - 12",
            rational_const(4),
            vec![("x + 1", 1), ("x^2 - 3", 1)],
        ),
        (
            "x^4 - 3*x^3 - 2*x^2 + 12*x - 8",
            rational_const(1),
            vec![("x + 2", 1), ("x - 1", 1), ("x - 2", 2)],
        ),
        (
            "x^4 + x^3 - 7*x^2 - x + 6",
            rational_const(1),
            vec![("x - 1", 1), ("x + 1", 1), ("x - 2", 1), ("x + 3", 1)],
        ),
        (
            "x^5 + x^4 - 2*x^3 - 2*x^2 + x + 1",
            rational_const(1),
            vec![("x - 1", 2), ("x + 1", 3)],
        ),
        (
            "x^4 - 10*x^2 + 9",
            rational_const(1),
            vec![("x - 3", 1), ("x + 3", 1), ("x - 1", 1), ("x + 1", 1)],
        ),
        (
            "x^3 - x^2 - x + 1",
            rational_const(1),
            vec![("x - 1", 2), ("x + 1", 1)],
        ),
        (
            "x^4 - 4*x^3 + 6*x^2 - 4*x + 1",
            rational_const(1),
            vec![("x - 1", 4)],
        ),
        (
            "2*x^4 - 3*x^3 - 11*x^2 + 3*x + 9",
            rational_const(2),
            vec![("x - 3", 1), ("x - 1", 1), ("x + 1", 1), ("x + 3/2", 1)],
        ),
        (
            "x^3 + x^2 - 4*x - 4",
            rational_const(1),
            vec![("x - 2", 1), ("x + 1", 1), ("x + 2", 1)],
        ),
        (
            "x^4 + 2*x^3 - x^2 - 2*x",
            rational_const(1),
            vec![("x", 1), ("x + 2", 1), ("x - 1", 1), ("x + 1", 1)],
        ),
        (
            "x^5 - 16*x",
            rational_const(1),
            vec![("x", 1), ("x - 2", 1), ("x + 2", 1), ("x^2 + 4", 1)],
        ),
        (
            "x^4 + 5*x^3 + 8*x^2 + 5*x + 1",
            rational_const(1),
            vec![("x + 1", 2), ("x^2 + 3*x + 1", 1)],
        ),
        (
            "x^4 - x^3 - 7*x^2 + x + 6",
            rational_const(1),
            vec![("x - 3", 1), ("x - 1", 1), ("x + 1", 1), ("x + 2", 1)],
        ),
        (
            "3*x^4 + x^3 - 16*x^2 - 4*x + 16",
            rational_const(3),
            vec![("x - 2", 1), ("x + 2", 1), ("x - 1", 1), ("x + 4/3", 1)],
        ),
        (
            "x^5 + 3*x^4 - 2*x^3 - 6*x^2 + x + 3",
            rational_const(1),
            vec![("x + 3", 1), ("x + 1", 2), ("x - 1", 2)],
        ),
        (
            "x^4 + 2*x^3 - 2*x^2 - 8*x - 8",
            rational_const(1),
            vec![("x^2 + 2*x + 2", 1), ("x - 2", 1), ("x + 2", 1)],
        ),
        (
            "x^4 + 4*x^3 + 3*x^2 - 4*x - 4",
            rational_const(1),
            vec![("x + 2", 2), ("x - 1", 1), ("x + 1", 1)],
        ),
    ];

    assert_eq!(cases.len(), 25);
    for (input, constant, factors) in cases {
        assert_factorization(input, constant, &factors);
    }
}
