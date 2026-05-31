//tipos indutivos via datatype
//tipo de dados imutável

datatype Cor = Azul | Amarelo | Vermelho | Verde

predicate Gremista(c:Cor)
{
  c.Azul?
}

method Main()
{
  var c1 := Azul;
  var c2 := Cor.Vermelho;
  assert Gremista(c1);
  assert !Gremista(c2);
}
