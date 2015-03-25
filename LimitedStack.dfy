// http://rise4fun.com/Dafny/TWQBT

// A LIFO queue (aka a stack) with limited capacity.
class LimitedStack{

      var capacity : int; // capacity, max number of elements allowed on the stack.
      var arr : array<int>; // contents of stack.
      var top : int; // The index of the top of the stack, or -1 if the stack is empty

      // This predicate express a class invariant: All objects of this calls should satisfy this.
      predicate Valid()
      reads this,this.arr;
      {
         arr != null &&  
         capacity > 0 &&
         capacity == arr.Length &&
         -1 <= top <= capacity-1
      } 
      
      predicate Empty()
      reads this, this.arr;
      {
         arr != null &&  
         capacity > 0 &&
         capacity == arr.Length &&
         top == -1
      }
      
      predicate Full()
      reads this, this.arr;
      {
       arr != null &&  
       capacity > 0 &&
       capacity == arr.Length && 
       top == (capacity-1) 
      }
     
      method Init(c : int)
      modifies this; //Note that Init methods always typically need to state that they will modify this object, as their purpose is to initialise all the fields. It also needs to specify that arr is a newly allocated array
      requires c > 0; 
      ensures capacity == c;
      ensures Empty();
      ensures fresh(arr); // ensures arr is a newly created object.
      {
        capacity := c;
        arr := new int[c];
        top := -1;
      }
   
      method isEmpty() returns (res : bool)
      requires this.Valid();
      ensures (top == -1) ==> (res == true);
      ensures !(top == -1) ==> (res == false);
      {
        if(top == -1){
          res := true;
        } else{
          res := false;
        }         
      }

      // Returns the top element of the stack, without removing it.
      method Peek() returns (elem : int)
      requires this.Valid();
      ensures Valid();
      ensures (top > -1) ==> elem == arr[top];
	  ensures top == old(top) && (forall i :: 0 <= i <= top ==> arr[i] == old(arr[i])); //ensure any of elements don't change.
      {
        if(top > -1){ //The stack is NOT empty
          elem := arr[top];
        }
        else{
          //The stack is empty
        }
      }

      // Pushed an element to the top of a (non full) stack. 
      method Push(elem : int)
      modifies this.arr, this`top;
      requires this.Valid();
	  requires top < capacity-1;
      ensures Valid();
      ensures (-1 <= old(top) < capacity-1) ==> ((top == old(top)+1) && (arr[top] == elem)) &&
			  (forall i :: 0 <= i < top ==> arr[i] == old(arr[i]));	//ensure other elements don't change.
      ensures (-1 > old(top) || old(top) > capacity-1) ==> top == old(top) &&
		  	  (forall i :: 0 <= i <= top ==> arr[i] == old(arr[i]));	//ensure any of elements don't change.
	  {
        if(-1 <= top < capacity-1){//The stack is NOT full
          top := top+1;			   //increment top of stack
          arr[top] := elem;		   //Set top to element
        }
        else{
		  //The stack is full
        }
      }

      // Pops the top element off the stack.
 
      method Pop() returns (elem : int)
      modifies this`top;
      requires this.Valid();
	  requires top > -1; //requires the stack is NOT empty
      ensures Valid();
      ensures (-1 < old(top) <= capacity-1) ==> ((elem == arr[old(top)]) && (top == old(top)-1));
	  ensures !(-1 < old(top) <= capacity-1) ==> (elem == -1) && top == old(top);
      {
        if(-1 < top <= capacity-1){ //The stack is NOT empty
          var tmp := arr[top];   //return value set to the last element 
          top := top-1;     //decrement top of stack 
		  elem := tmp;
		  return;
        }
        else{
		  return ;
        }
      }

      //Push onto full stack, oldest element is discarded.
      
      method Push2(elem : int)
      modifies this.arr, this`top;
      requires Valid();
      ensures Valid();
     // ensures (top == capacity-1) ==> forall i :: 1 <= i <= top ==> arr[i] == old(arr[(i)]);
	  ensures (top == capacity-1) ==> Full() && arr[top] == elem &&
			  (forall k :: 0 <= k < top ==> arr[k] == old(arr[k+1]));	//ensure elements[0,top) have changed.
      ensures (top != capacity-1) ==> top == old(top) &&
		  	  (forall i :: 0 <= i <= top ==> arr[i] == old(arr[i]));	//ensure any of elements don't change.
      {
        var i := 1;
        if(top == capacity-1){
          forall(i | 1 <= i <= top){            
            arr[i-1] := arr[i];
          }
          arr[top] := elem;
        }
        else{
          //The stack is NOT full 
        }
      }




// When you are finished,  all the below assertions should be provable. 
// Feel free to add extra ones as well.
      method Main(){
           var s := new LimitedStack;
           s.Init(3);

           assert s.Empty() && !s.Full(); 

           s.Push(27);
           assert !s.Empty();
           assert s.arr[0] == 27;

           var e := s.Pop();
           assert s.Empty();
           assert e == 27;
		   assert s.arr[0] == 27;
		   
		   s.Push(5);
		   assert !s.Empty();
           assert s.arr[0] == 5;
           s.Push(32);
		   assert s.arr[0] == 5;
		   assert s.arr[1] == 32;
           s.Push(9);
		   assert s.arr[2] == 9;
           assert s.Full();
		   assert s.arr[0] == 5;

           var e2 := s.Pop();
           assert !s.Full();
           assert e2 == 9; 
           assert s.arr[0] == 5;
		   
           s.Push(e2);
           s.Push2(99);

           var e3 := s.Peek();
           assert e3 == 99;
           assert s.arr[0] == 32;
                     
       }

}