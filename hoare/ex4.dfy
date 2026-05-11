method Exemplo(x:int) returns (r:int)
  ensures r >= 0
{
    assert (x < 0 ==> -x >= 0) && (!(x < 0) ==> x >= 0);
    r := x;
    assert (x < 0 ==> -x >= 0) && (!(x < 0) ==> r >= 0);
    if x < 0
    {
        assert -x >= 0;
        r := -x;
        assert r >= 0;
    }
    assert r >= 0;
}
