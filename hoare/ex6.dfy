ghost function Fact(n:nat):nat
{
    if n == 0
    then 1
    else n * Fact(n-1)
}

method Exemplo(n:nat) returns (f:nat)
    ensures f == Fact(n)
{
    assert 0 <= n && 1 == Fact(0);
    assert 1-1 <= n && 1 == Fact(1-1);
    var i := 1;
    assert i-1 <= n && 1 == Fact(i-1);
    f := 1;
    assert i-1 <= n && f == Fact(i-1); 
    while i <= n
      invariant i - 1 <= n
      invariant f == Fact(i-1)
    {
        assert i <= n && i - 1 <= n && f == Fact(i-1);
        assert i <= n && f*i == Fact(i);
        f := f * i;
        assert i <= n && f == Fact(i);
        assert i+1-1 <= n && f == Fact(i+1-1);
        i := i + 1;
        assert i-1 <= n && f == Fact(i-1);
    }
    assert i > n && i - 1 <= n && f == Fact(i-1);
    assert f == Fact(n);
}