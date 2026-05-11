method Triple(x: int) returns (r: int)
  requires true
  ensures r == 3*x
{
    assert x+2*x == 3*x; //obtido pelo cálculo da precondição mais fraca via Floyd-Hoare
    var y := 2*x;
    assert x+y == 3*x;
    r := x + y;
    assert r == 3*x;
}

// A condição de verificação para a correção é:
// true ==> x+2*x == 3*x
