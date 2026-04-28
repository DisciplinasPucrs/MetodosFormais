method Exemplo(x:int, y:int) returns (r:int)
  requires x > 2 && y > 3
  ensures r > 6
{
    assert y + x + 1 > 6;
    var w := x + 1;
    assert y + w > 6;
    r := y + w;
    assert r > 6;
}
