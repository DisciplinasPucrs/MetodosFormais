ghost function Fatorial(n:nat):nat
{
    if n == 0
    then 1
    else n * Fatorial(n-1)
}

method Fat(n:nat) returns (r:nat)
ensures r == Fatorial(n)
{
    r := 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant r == Fatorial(i)
    {
        i := i + 1;
        r := r * i;
    }
}
