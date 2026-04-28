ghost function Fatorial(n:nat):nat
{
    if n == 0
    then 1
    else n * Fatorial(n-1)
}

method Fat(n:nat) returns (f:nat)
ensures f == Fatorial(n)
{
    var i := 1;
    f := 1;
    while i <= n
      invariant f == Fatorial(i-1)
      invariant 1 <= i <= n+1
    {
        f := f * i;
        i := i + 1;
    }
}