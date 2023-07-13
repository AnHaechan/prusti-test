use prusti_contracts::*;

// Restrictive precondition
#[requires(x == 10)]
#[ensures(result == x * x)]
pub fn restrictive_square(x: i32) -> i32 {
    x * x
}

// fn test() {
//     assert!(restrictive_square(10) == 100);
//     assert!(restrictive_square(5) == 25);
// }

// Incomplete postcondition
#[pure]
#[ensures(x >= 0 ==> result == x)]
pub fn abs (x: i32) -> i32 {
    x
}

// fn test_abs() {
//     prusti_assert!(abs(8) == 8);
//     prusti_assert!(abs(-10) == 10);
// }