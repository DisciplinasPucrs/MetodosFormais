ghost function Sum(n:nat):nat
{
    if n == 0
    then 0
    else Sum(n-1) + n
}

method Compute_Sum(n:nat) returns (s:nat)
ensures s == Sum(n)
{
    s := 0;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant s == Sum(i)
    {
        i := i + 1;
        s := s + i;
    }
}

method Teste()
{
    var n := 3;
    var s := Compute_Sum(n);
    assert s == 6;
}