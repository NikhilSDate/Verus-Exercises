use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n,
{
    if n < 2 { n } else { fib((n - 2) as nat) + fib((n - 1) as nat) }
}

proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fib(i) <= fib(j),
    decreases j - i,
{
    // TODO: prove by induction on j - i
}

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
            // TODO
    {
        // TODO
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
