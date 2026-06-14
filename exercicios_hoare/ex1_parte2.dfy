ghost function Pot(a:nat, b:nat):nat
{
  if (b == 0)
  then 1
  else a * Pot(a, b-1)
}

method Exercicio(a:int, b:int) returns (p:int)
  requires a > 0 && b >= 0
  ensures p == Pot(a,b)
{
    assert 0<=b && 1==Pot(a,0);
    var i := 0;
    assert i<=b && 1==Pot(a,i);
    p := 1;
    assert i<=b && p==Pot(a,i);
    while i < b
      invariant i <= b
      invariant p == Pot(a,i)
    {
        assert i<b && p==Pot(a,i);
        assert i+1<=b && p*a==Pot(a,i+1);
        p := p * a;
        assert i+1<=b && p==Pot(a,i+1);
        i := i + 1;
        assert i<=b && p==Pot(a,i);
    }
    assert !(i<b) && i<=b && p==Pot(a,i);
}