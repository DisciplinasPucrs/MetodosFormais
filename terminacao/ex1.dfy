function Somar(m:nat, n:nat):nat
  decreases m
  ensures Somar(m,n) == m+n
{
  if (m == 0)
  then n
  else Somar(m-1,n) + 1
}
