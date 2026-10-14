use std::println;

use vstd::prelude::*;

verus! {

// spec: the mathematical definition
spec fn fib(n: nat) -> nat
    decreases n,
{
    if n < 2 { n } else { fib((n - 2) as nat) + fib((n - 1) as nat) }
}

// proof: fib is monotonic
proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
    decreases j - i,
{
    if i < j {
        lemma_fib_monotonic(i, (j - 1) as nat);
    }
}

// exec: iterative computation that never overflows
fn fib_iter(n: u64) -> (r: u64)
    requires
        fib(n as nat) <= u64::MAX,
    ensures
        r == fib(n as nat),
{
    if n == 0 {
        return 0;
    }
    let mut prev: u64 = 0;
    let mut cur: u64 = 1;
    for i in 1..n
        invariant
            fib(n as nat) <= u64::MAX,
            prev == fib((i - 1) as nat),
            cur == fib(i as nat),
    {
        proof {
            lemma_fib_monotonic((i + 1) as nat, n as nat);
        }
        let next = prev + cur;
        prev = cur;
        cur = next;
    }
    cur
}

fn main() {
    assert(fib(10) == 55) by (compute);
    let x = fib_iter(10);
    assert(x == 55);
}

} // verus!
