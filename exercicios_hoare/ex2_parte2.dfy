method Exercicio(x:int) returns (y:int)
  requires x >= 0
  ensures y == x
{
    assert x==x;
    var a := x;
    assert a==x;
    y := 0;
    assert y+a==x;
    while a != 0
      invariant y + a == x
    {
        assert a!=0 && y+a==x;
        assert y+1+a-1==x;
        y := y + 1;
        assert y+a-1==x;
        a := a - 1;
        assert y+a==x;
    }
    assert !(a!=0) && y+a==x;
}