class CircularMemory{
    
    var cells : array<int>
    var read_position : int
    var write_position : int
    var isFlipped : bool


    constructor Init(cap : int)
        requires cap > 0
        ensures Valid()
    {
        cells := new int[cap];
        read_position, write_position := 0, 0;
        isFlipped := false;
    }

    predicate Valid() 
        reads this
    {
        (read_position >= 0 && read_position < cells.Length) &&
        (write_position >= 0 && write_position < cells.Length) &&
        (cells.Length > 0)
        //(read_position % cells.Length < cells.Length) && (read_position % cells.Length >= 0)
        //(isFlipped ==> write_position < read_position) &&
        //(!isFlipped ==> write_position >= read_position) 
    }

    // A predicate indicating no more Read available
    predicate isEmpty()
        reads this
        requires Valid()
        ensures Valid()
    {
        (read_position == write_position)
    }

    //A predicate indicating no more Write should be allowed
    predicate isFull()
        reads this
        requires Valid()
        ensures Valid()
    {
        (write_position + 1 % cells.Length == read_position)
    }

    method Read() returns (isSuccess : bool, content : int)
        modifies this
        requires Valid()
        ensures  Valid()
        ensures isSuccess  ==> read_position == old(read_position) + 1 % cells.Length 
        ensures isSuccess  ==> content       == cells[old(read_position)]
        ensures !isSuccess ==> read_position == old(read_position)
        ensures !isSuccess ==> content       == -100
    {
        isSuccess := false;
        content := -100;

        if(!(write_position + 1 % cells.Length == read_position)){
            if(read_position >= 0 && read_position < cells.Length){
                content       := cells[read_position];
                read_position := read_position + 1 % cells.Length;
                isSuccess     := true;
                return isSuccess, content;  
            }
        }else { 
            return isSuccess, -100;
        }
    }
}
    /*
    method Write(input : int) returns (isSuccess : bool)
        modifies this
        requires Valid()
        requires isFull()
        ensures  Valid()
        ensures isFull()
        ensures  isSuccess ==> cells[write_position] == input
        ensures !isSuccess ==> cells[write_position] != input
    
    {
        if(!isFull()){
            return false;
        } else if(write_position == read_position){
            cells[write_position] := input;
            write_position := write_position + 1;
            return true;
        } else {
            return false;
        }
    }
    */