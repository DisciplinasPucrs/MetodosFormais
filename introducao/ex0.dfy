function Somar(m:nat, n:nat):nat
//A verificação depende da implementação concreta; diz-se que funções são transparentes
{
  if (m == 0)
  then n
  else Somar(m-1,n) + 1
}

predicate Par(x:nat)
//A verificação depende da implementação concreta; diz-se que predicados são transparentes
{
  x % 2 == 0
}
