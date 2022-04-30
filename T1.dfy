class{:autocontracts} Pilha
{
    var vetor: array<int>;
    var cardinalidade : int;
    var maxSize : int;
    ghost var Conteudo: seq<int>;
    ghost const TamanhoMaximo: nat;

    predicate Valid()
    {
        maxSize > 0
        && vetor.Length == maxSize
        && 0 <= cardinalidade <= vetor.Length
        && vetor[0..cardinalidade] == Conteudo
        && cardinalidade == |Conteudo|
        && vetor.Length == TamanhoMaximo
    }

    constructor(m:int)
    requires m > 0
    ensures Conteudo == []
    ensures |Conteudo| == 0
    ensures maxSize == TamanhoMaximo
    {
        maxSize := m;
        vetor := new int[m];
        cardinalidade := 0;
        Conteudo := [];
        TamanhoMaximo := maxSize;
    }

//Adiciona um elemento no topo da Pilha
method Push(e:int) returns (b:bool)
    //Verifica que se a cardinalidade for igual ao tamanho ele retorna False e o conteudo continua o mesmo
    ensures old(cardinalidade) == TamanhoMaximo  ==> ((Conteudo == old(Conteudo)) && b == false)
    //Verifica que se a pilha não está cheia, o elemento é inserido e a cardinalidade modificada
    ensures old(cardinalidade) < TamanhoMaximo ==> Conteudo == old(Conteudo) + [e] 
              && b == true && cardinalidade == old(cardinalidade) + 1
    {
        if(cardinalidade == vetor.Length){
            return false;
        }
        vetor[cardinalidade] := e;
        cardinalidade := cardinalidade +1;
        Conteudo := Conteudo + [e];
        return true;
    }

//Remove o elemento do topo da pilha
method Pop() returns (e:int)
    //Verifica se a pilha não está vazia
    requires cardinalidade > 0
    requires |Conteudo| > 0
    //Verifica se foi removido o elemento e a cardinalidade diminuiu
    ensures cardinalidade == old(cardinalidade)-1 && |Conteudo| == old(|Conteudo|)-1
    ensures e == old(vetor[cardinalidade-1])
    {
        e := vetor[cardinalidade-1];
        cardinalidade := cardinalidade-1;
        Conteudo := vetor[..cardinalidade];
    }

//Apenas olha o elemento no topo da lista se ele existe
method Peek() returns(e:int)
    //verifica se a pilha não está vazia
    requires cardinalidade > 0
    requires |Conteudo| > 0

    //verifica se todos atributos continuam iguais
    ensures cardinalidade == old(cardinalidade)
    ensures Conteudo == old(Conteudo)
    ensures vetor == old(vetor)
    ensures e == vetor[cardinalidade-1]
    {
    return vetor[cardinalidade-1];
    }
    
   
    //Retorna o tamanho maximo da pilha
    method maximumSize() returns (n:int)
    ensures n == TamanhoMaximo
    ensures Conteudo == old(Conteudo)
    {
        return maxSize;
    }
    
    //Retorna quantos elementos tem na pilha
    method Size() returns (n:int)
    ensures n == |Conteudo|
    ensures Conteudo == old(Conteudo)
    {
        return cardinalidade;
    }

    //Retorna se a pilha está vazia
    method isEmpty() returns (b:bool)
    //Verifica que vai ser verdade se e somente se a cardinalidade for zero e o conteúdo estiver vazio
    ensures b == (cardinalidade == 0 && Conteudo == [])
    { 
            return (vetor.Length == 0 || cardinalidade ==0);
    }

    //Retorna se a pilha está cheia
    method isFull() returns (b:bool)
     //Verifica que vai ser verdade se e somente se a cardinalidade for igual ao tamanho maximo
    ensures b == (cardinalidade == vetor.Length) 
    {
        return (cardinalidade == vetor.Length);   
    }

    //Inverte a pilha atual
    method reverse() returns ()
    ensures Conteudo == old(Conteudo[cardinalidade..0])
    ensures |Conteudo| == old(|Conteudo|)
    ensures cardinalidade == old(cardinalidade)
    {
        var auxVet := new int[maxSize];
        forall i | 0 <= i < cardinalidade
        {
            auxVet[i] = pilha.pop();
        }
        Conteudo := old(Conteudo[cardinalidade..]);

    }

}
    


method Main()
{
        var testePilha := new Pilha(5);
        var card := testePilha.Size();
        var isEmpty := testePilha.isEmpty();
        var isFull := testePilha.isFull();
        print(isFull);

        assert card == 0;
        assert isEmpty == true;
        assert isFull == false;

        var adiciona := testePilha.Push(3);
        isEmpty := testePilha.isEmpty();
        card := testePilha.Size();

        assert adiciona == true;
        assert isEmpty == false;
        assert card == 1;

        var d:= testePilha.Peek();
        assert d == 3;

        var remove := testePilha.Pop();
        card := testePilha.Size();
        isEmpty := testePilha.isEmpty();
        assert card == 0;
        assert isEmpty == true;
        assert isFull == false;
        assert remove == 3;

}

