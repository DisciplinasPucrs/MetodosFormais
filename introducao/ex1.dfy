method Triple(x: int) returns (r: int)
  requires true //pode ser removido, é a condição padrão
  ensures r == 3*x
{
  var y := 2*x;
  r := x + y; //return x + y;
}
