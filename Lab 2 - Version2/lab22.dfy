http://rise4fun.com/Dafny/jfn4U

class Token
{
	var	clearLevel:	int;
	var id: int; //This is stored fingerprint on token
  var valid: bool;
	
	constructor(t: int, cl: int)
	modifies this`valid,this`id,this`clearLevel;
	requires 0 <= cl <= 3; //0 : Error - 1: Low - 2: Medium - 3: High
  ensures valid == true;
	ensures id == t;
	ensures clearLevel == cl;
	{
		valid := true;
		id := t;
		clearLevel := cl;
	} 
} 
  
class EnrolStation
{
  var tokens: set<int>;
  
  constructor()
  modifies this`tokens;
  ensures tokens == {};
  {
    tokens := {};
  }
  
	method CreateToken(fp: int, cl: int) returns (res: Token)
	modifies this`tokens;
	requires 0 <= cl <= 3;
  ensures res != null;
  ensures res.valid == true;
  ensures (fp !in old(tokens)) ==> res.id == fp && res.clearLevel == cl && tokens == old(tokens) + {fp};
	ensures (fp in old(tokens)) ==>  res.id == 0 && res.clearLevel == 0 && tokens == old(tokens);
  ensures fresh(res);
	{
		if(fp !in tokens){
		  tokens := tokens + {fp};
      res := new Token(fp, cl);
		}
		else {
      res := new Token(0, 0);
		}
	}
}

class IdStation
{
  //var rToken: Token;
	var clearLevel : int;
	var alarm: bool;
	var	accepted:	bool;
	
	predicate close()
	reads this;
	{
		accepted == false &&
		alarm == false
	
	}
	
	method Init(cl: int)
	modifies `accepted, `alarm,`clearLevel;
  requires 0 <= cl <= 3;
	ensures close();
	ensures clearLevel == cl;
	{
	  accepted := false;
		alarm := false;
		clearLevel := cl;
	}	
  
	method Authentication(token:Token, fp:int)
	modifies this`accepted, this`alarm, token`valid;	
  requires token != null;
  requires token.valid == true;
  requires close();
	ensures	token.id == fp && token.clearLevel == clearLevel ==> 
				accepted == true && alarm == false && token.valid == true;
	ensures token.id != fp ==> 
			accepted == false && alarm == true && token.valid == false;
	ensures token.id == fp  && token.clearLevel != clearLevel ==> 
			accepted == false && alarm == false && token.valid == true;
	{
		if(token.id == fp){
			if(token.clearLevel == clearLevel){
				accepted := true;
				alarm := false;
			}
			else{
				accepted := false;
				alarm := false;
			}
		}
		else{
			accepted := false;
			alarm := true;
			token.valid := false;
		}
	}	
}

method	Main()
	{
		var enrol := new EnrolStation();
    var idStation := new IdStation;
    var	tokenCase1 : Token;
    var	tokenCase2 : Token;
    var	tokenCase3 : Token;
		var	tokenCase4 : Token;
    
		//CASE 1 - DENIED AUTHENTICATION, WRONG FINGERPRINT
		tokenCase1 := enrol.CreateToken(1234, 1);
    assert tokenCase1.id == 1234;
    assert tokenCase1.clearLevel == 1;
    idStation.Init(1);
    assert idStation.clearLevel == 1;
    idStation.Authentication(tokenCase1, 4321);
    assert tokenCase1.id == 1234;
    assert idStation.clearLevel == 1;
		assert idStation.accepted == false;
    assert idStation.alarm == true;
    assert tokenCase1.valid == false;
   
		//CASE 2 - DENIED AUTHENTICATION, WRONG CLEARENCE-LEVEL
		tokenCase2 := enrol.CreateToken(2345, 1);
    assert tokenCase2.id == 2345;
    assert tokenCase1.clearLevel == 1;
    idStation.Init(2);
    assert idStation.clearLevel == 2;
    idStation.Authentication(tokenCase2, 2345);
    assert tokenCase2.id == 2345;
    assert idStation.clearLevel == 2;
		assert idStation.accepted == false;
    assert idStation.alarm == false;
    assert tokenCase2.valid == true;
    
    

		//CASE 3 - DENIED AUTHENTICATION, WRONG TOKEN-NUMBER
		tokenCase3 := enrol.CreateToken(3456, 3);
    idStation.Init(3);
    idStation.Authentication(tokenCase2, 3456); //The fingerprint belongs to user3 which try to open the door with wrong token.
		assert idStation.accepted == false;
    assert idStation.alarm == true;
    assert tokenCase2.valid == false;
		
		//CASE 4 - ACCEPTED AUTHENTICATION
		tokenCase4 := enrol.CreateToken(5555, 3);
    idStation.Init(3);
    idStation.Authentication(tokenCase4, 5555); 
		assert idStation.accepted == true;
    assert idStation.alarm == false;
    assert tokenCase4.valid == true;
        		
	}

