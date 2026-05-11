method Exemplo(x0:int, y0:int) returns (x:int, y:int)
  ensures x <= y
  ensures (x == x0 && y == y0) || (x == y0 && y == x0)
{
    assert x0 > y0 ==> y0 <= y0 &&  ((y0 == x0 && x0 == y0) || (y0 == y0 && x0 == x0));
    x := x0;
    assert x > y0 ==> y0 <= y0 &&  ((y0 == x0 && x == y0) || (y0 == y0 && x == x0));
    y := y0;
    assert x > y ==> y <= y &&  ((y == x0 && x == y0) || (y == y0 && x == x0));
    if (x > y)
    {
        assert y <= y &&  ((y == x0 && x == y0) || (y == y0 && x == x0));
        var z := y;
        assert z <= x &&  ((z == x0 && x == y0) || (z == y0 && x == x0));
        y := x;
        assert z <= y &&  ((z == x0 && y == y0) || (z == y0 && y == x0));
        x := z;
        assert x <= y &&  ((x == x0 && y == y0) || (x == y0 && y == x0));
    }
    assert x <= y &&  ((x == x0 && y == y0) || (x == y0 && y == x0));
}
