class CircularMemory{
    
    var cells : array<int>
    var read_position : int
    var write_position : int
    var isFlipped : bool


    constructor Init(cap : int)
    //missing some pre-conditions here
    {
        cells := new int[cap];
        read_position, write_position := 0, 0;
        isFlipped := false;
    }

}