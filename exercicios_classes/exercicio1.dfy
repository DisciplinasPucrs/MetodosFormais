class WrapArray
{
  var intarray: array<int>
  constructor (i:int) 
    requires i > 0
  {
    intarray := new int[i];
  }
  method init(i: int)
    modifies intarray
  {
    var index: int := 0;
    while (index < intarray.Length)
    {
      intarray[index] := i;
      index := index+1;
    }
  }
}

method Main()
{
  var sh:= new WrapArray(5);
  sh.init(4);
}

/*
Quando o dafny é solicitado a verificar isso, ele reclama da chamada sh.init que modifica objetos que o Main não permite.
De fato, sh.init modifica os elementos de sh.intarray e diz isso em sua cláusula modifies, mas esse array nem sequer existe, nem sh em escopo, no pré-estado de Main.
O Main deve poder modificar objetos que são alocados após o pré-estado. De fato, o Main sabe que sh é recém-alocado, então seus campos podem ser alterados.
Ou seja, podemos atribuir a sh.intarray. Mas aqui queremos mudar o estado do sh.intarray, não do sh. O array é recém-alocado, mas o Main não sabe disso.
Afinal, é possível que o construtor tenha inicializado o sh.intarray com algum array já existente e mudar os elementos desse array altere o estado de algum outro objeto.
Precisamos informar ao Main que o construtor do WrapArray aloca um novo array de ints.
A sintaxe para fazer isso é adicionar uma poscondição ao construtor que diz fresh(intarray).
*/
/*
Além do problema do frame, observe que não foi especificado nenhum tipo de poscondição dos métodos.
Logo, não se consegue verificar nada sobre o resultado do uso dos métodos dentro do Main.
*/