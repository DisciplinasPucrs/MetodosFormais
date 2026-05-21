function tail_len<T>(lista:seq<T>, a:nat):nat
  decreases lista
{
  if |lista| == 0
  then a
  else tail_len(lista[1..], a+1)
}
