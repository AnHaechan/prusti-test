use prusti_contracts::*;

fn main() {
    let _ = max (3, 10);
}

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

#[ensures(result == max(a, max(b, c)))]
fn max3(a: i32, b: i32, c: i32) -> i32 {
    if a > b && a > c {
        a
    } else {
        if b > c {
            b
            // assert!(max(b, c) == c); // FAILS
            // c
        } else {
            c
        }
    }
}