var searchIndex = JSON.parse('{\
"tokyodoves":{"doc":"Crate Description","t":"NEIDDDDDDNDDNEDEDDDNNDDENNNNNNNNNNDNNDENNENLLCLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLFKLLLLLLLLMLLLMLLLLLLLLLLALLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLMMLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLKLLLLLLLLLLLLLKLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLCCLLLCLLLLLLLLLLLLLLLLLLLLLLLLLAFLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLMMLLLLENENNEENNNNNNNNNNENENNNNNNNNNNNNNENENNNNLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLMMMMMMMMNCENECECCNCCCDDNNCCNNNNALLLLLLLLLLLLLLLLFLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLMDDDDDDDDDDDDDDDDDLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLL","n":["A","Action","ActionContainer","ActionsBwd","ActionsBwdIntoIter","ActionsBwdIter","ActionsFwd","ActionsFwdIntoIter","ActionsFwdIter","B","Board","BoardBuilder","Both","Color","ColorIter","Dove","DoveIter","DoveSet","DoveSetIntoIter","Draw","Draw","Game","GameRule","GameStatus","Green","H","LastPlayer","M","Move","NextPlayer","None","OneSide","Ongoing","Put","Rectangle","Red","Remove","Shift","SurroundedStatus","T","Win","WinnerJudgement","Y","add","allow_remove","array_macro","board","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","build","build_unchecked","check_action","check_action_bwd","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","color_dove_to_char","contains","contains","contains","contains","count_doves_on_field","count_doves_on_field_of","default","default","default","dh","dove","doves_in_hand_of","doves_on_field_of","dv","empty","eq","eq","eq","eq","eq","eq","eq","eq","eq","error","first_player","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from_rule","from_ssn","from_str","from_u16_bits","from_u64","from_u64_bits","hash","hash","hash","hash","hash","hash","hash","hash","hash","hmax","hmin","index","index","initial_board","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","is_empty","is_empty","is_empty","is_empty","is_in_hand","is_on_field","is_ongoing","iter","iter","iter","iter","legal_actions","legal_actions","legal_actions_bwd","len","len","len","len","len","len","liberty","liberty_of_boss","minimum_rectangle","neg","new","new","new","next","next","next","next","next","next","next","next_back","next_back","next_player","not","nth","nth","perform","perform","perform_bwd","perform_bwd_copied","perform_copied","perform_unchecked","perform_unchecked_copied","player","position_in_rbcc","prune_outside_4x4","put_dove","remove_dove","reset","rule","set_allow_remove","shift","simultaneous_surrounding","size","size_hint","size_hint","status","strum","strum_macros","sub","surrounded_status","swap_color","thiserror","to_4x4_matrix","to_framed_string","to_invariant_u64","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_simple_string","to_ssn","to_string","to_string","to_u64","tools","try_char_to_color_dove","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from_4x4_matrix","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","vmax","vmin","winner","with_first_player","with_initial_board","with_simultaneous_surrounding","ActionConvertError","ActionPerformError","ActionPerformErrorType","AlreadyOnBoard","BoardCreateError","BoardCreateErrorType","BoardError","BoardError","BossNotFound","BossNotFound","BossNotFound","ColorNotInferred","DoveDuplicated","DoveIsolated","DoveNotFound","DoveNotInferred","DoveNotOnBoard","GameError","GameFinishedError","GameRuleError","InitialBoardError","InvalidPosition","InvalidShift","MaskShiftError","NotOnBoard","NumberNotFollowAfterNEWS","ObstacleInRoute","OutOfField","PlayerMismatchError","PositionDuplicated","PositionOutOfRange","ProhibitedRemoveError","SSNDecodingError","SSNDecodingErrorType","SSNEncodingError","SSNEncodingErrorType","ThroughOuterField","ToBeIsolated","TriedToRemoveBoss","UnexpectedCharacter","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","clone","clone","clone","clone","clone","clone","clone","clone","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","clone_into","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","fmt","from","from","from","from","from","from","from","from","into","into","into","into","into","into","into","into","provide","provide","provide","provide","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_owned","to_string","to_string","to_string","to_string","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","error_type","error_type","action","error_type","error_type","action","error","game_status","BoardAlreadyFinished","BoardSet","BoardValue","BoardValueError","BoardValueErrorType","Capacity","CompareBoardValueError","Difference","Drain","DrawNotSupportedError","Intersection","IntoIter","Iter","LazyBoardLoader","LazyRawBoardLoader","Lose","LoseArgMustPositiveEven","SymmetricDifference","Union","Unknown","UnknownNotSupported","Win","WinArgMustOdd","board_set","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","clone","clone","clone","clone_into","clone_into","clone_into","compare_board_value","fmt","fmt","fmt","fmt","fmt","fmt","from","from","from","from","from","from","into","into","into","into","into","into_iter","into_iter","into_raw","new","new","next","next","provide","raw","raw_mut","to_owned","to_owned","to_owned","to_string","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_next","try_next","type_id","type_id","type_id","type_id","type_id","error_type","BoardSet","Capacity","Difference","Drain","Intersection","IntoIter","Iter","RawBoardSet","RawDifference","RawDrain","RawIntersection","RawIntoIter","RawIter","RawSymmetricDifference","RawUnion","SymmetricDifference","Union","absorb","absorb","add","add_assign","bitand","bitand","bitor","bitor","bitxor","bitxor","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","capacity","capacity","clear","clear","clone","clone","clone","clone_into","clone_into","clone_into","contains","contains","default","default","default","difference","difference","drain","drain","extend","extend","fmt","fmt","fmt","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from","from_iter","from_iter","insert","insert","intersection","intersection","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_raw","is_disjoint","is_disjoint","is_empty","is_empty","is_empty","is_subset","is_subset","is_superset","is_superset","iter","iter","len","len","len","load","load","load_filter","load_filter","new","new","new","next","next","next","next","next","next","next","next","next","next","next","next","next","next","raw","raw_mut","remove","remove","required_capacity","required_capacity","required_capacity_filter","required_capacity_filter","reserve","reserve","retain","retain","save","save","symmetric_difference","symmetric_difference","take","take","to_owned","to_owned","to_owned","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","type_id","union","union","with_capacity","with_capacity"],"q":[[0,"tokyodoves"],[420,"tokyodoves::error"],[560,"tokyodoves::error::ActionConvertError"],[562,"tokyodoves::error::BoardError"],[565,"tokyodoves::error::GameError"],[568,"tokyodoves::tools"],[657,"tokyodoves::tools::CompareBoardValueError"],[658,"tokyodoves::tools::board_set"]],"d":["Represents <strong>A</strong>niki-hato, which can move to adjacent squares …","Actions players can perform in their turn.","Read-only <code>Sized</code> container of <code>Action</code>s.","An <code>ActionContainer</code> returned by <code>Board::legal_actions_bwd</code>","An <code>Iterator</code> returned by <code>ActionsBwd::into_iter</code>","An <code>Iterator</code> returned by <code>ActionsBwd::iter</code>","An <code>ActionContainer</code> returned by <code>Board::legal_actions</code>","An <code>Iterator</code> returned by <code>ActionsFwd::into_iter</code>","An <code>Iterator</code> returned by <code>ActionsFwd::iter</code>","Represents <strong>B</strong>oss-hato, which can move to adjacent squares …","An implementation of Tokyo Doves board based on bitboard …","A builder of <code>Board</code>","","Two colors of player, just like black and white in chess.","An iterator over the variants of Color","Six types of doves.","An iterator over the variants of Dove","Read-only <code>Sized</code> container of <code>Dove</code>s without duplication.","An <code>Iterator</code> returned by <code>DoveSet::into_iter</code>","It is a draw game","The game has already finished; it was a draw game","A struct that provides methods to play Tokyo Doves games …","Some kinds of detailed rules","Status of the game","","Represents <strong>H</strong>ajike-hato, which can move (or jump) like the …","The player just before the event is treated as the winner","Represents <strong>M</strong>amedeppo-bato, which can move to four …","Move <code>Color</code>’s <code>Dove</code> on the board toward <code>Shift</code> from its …","The player just after the event is treated as the winner","","","The game is ongoing","Put <code>Dove</code> from <code>Color</code>’s hand on the board at the position …","Rectangle with edges of <code>usize</code> coordinates.","","Remove <code>Color</code>’s <code>Dove</code> from the board (which returns to …","Difference between two squares.","An enum returned by <code>Board::surrounded_status</code>","Represents <strong>T</strong>otsu-hato, which can move forward, backward or …","The game has already finished; one player defeated the …","Judgement of winner on some event","Represents <strong>Y</strong>aibato, which can move to four adjacent …","","","","Get a reference to board","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Check if <code>action</code> is legal.","Check if backward <code>action</code> is legal.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Returns <code>true</code> if it contains the specified <code>Action</code>.","Returns <code>true</code> if it contains the specified <code>Dove</code>.","","","Counts the number of all doves on the field.","Counts the number of doves of the <code>player</code> on the field.","","","Returns the default value.","Horizontal shift. Positive (or negative) direction is on …","","Collects and returns the set of doves in the <code>player</code>’s …","Collects and returns the set of doves of the <code>player</code> on the …","Vertical shift. Positive (or negative) direction is on …","","","","","","","","","","","Error variants","","","","","","","","","","","","","","","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","","Returns the argument unchanged.","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Constructs <code>Game</code> with a specified <code>rule</code>","Creates <code>Action</code> from <code>&amp;str</code> in Standard Short Notation (SSN)","","Create <code>BoardBuilder</code> by indicating positions of doves in <code>u16</code>…","Alias of <code>from::&lt;u64&gt;</code>","Create <code>BoardBuilder</code> by indicating positions of doves in <code>u64</code>…","","","","","","","","","","The maximum coordinate in horizontal direction","The minimum coordinate in horizontal direction","","","","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","Returns <code>true</code> if it is empty.","Returns <code>true</code> if it is empty.","","","Returns <code>true</code> if the <code>player</code>’s <code>dove</code> is in their hand.","Returns <code>true</code> if the <code>player</code>’s <code>dove</code> is on the field.","Returns <code>true</code> if the game is ongoing","","","","","Collects and returns the set of all legal <code>Action</code>s for the …","Returns an <code>ActionContainer</code> of legal <code>Action</code>s.","Collects and returns the set of all legal backward-<code>Action</code>s …","Returns the number of elements.","Returns the number of elements.","","","","","Returns “liberty” of <code>player</code>’s <code>dove</code>, where liberty is …","Returns “liberty” of <code>player</code>’s boss-hato.","Returns the minimum rectangle that contains all doves on …","","","Constructs <code>GameRule</code> object","Constructs <code>Game</code>","","","","","","","","","","Get a reference to the next player","","","","Performs the specified <code>action</code> to <code>self</code>.","Performs <code>action</code>.","Performs the specified backward action to <code>self</code>.","Returns the result of performing the specified backward …","Returns the result of performing the specified action to …","Performs <code>action</code> to <code>self</code> (without distinction between …","Returns the result of performing the specified action to …","","Returns the position of specified player and dove in …","","","","Reset <code>Game</code> to the initial state","Get a reference to game rule","Update whether allow <code>Remove</code> in the game or not","","","Calculates the lengths of horizontal and vertical edges.","","","Get a reference to status","","","","Get info whether bosses are surrounded or not","Swaps the colors red and green.","","Returns 4x4 matrix (array of array) representing the board.","Returns a <code>String</code> expression with a frame.","Returns a light expression of <code>u64</code> with a universality.","","","","","","","","","","","","","","","","","","","Converts <code>self</code> into <code>String</code> in Standard Short Notation (SSN)","","","Returns a light expression of 64 bits.","Convenient tools to analyze the game","","","","","","","","","","","","","","","","","","","","","","","","","Alias of <code>try_from::&lt;..&gt;</code>","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","The maximum coordinate in vertical direction","The minimum coordinate in vertical direction","Returns winner.","Update the player moving firstly in the beginning of the …","Update initial_board of <code>GameRule</code>","Update judgement rule when both bosses are surrounded …","Errors on conversion between <code>Action</code> and string in SSN","","Types of errors on performing <code>Action</code>","","","Types of errors on creating <code>Board</code>","Errors associated to <code>Board</code>","","","","","","","","","","","Errors associated to <code>Game</code>","","Errors associated to <code>GameRule</code>","","","","","","","","","","","","","","Types of errors on conversion of <code>Action</code> from string in SSN","","Types of errors on conversion of <code>Action</code> into string in SSN","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Value of board","","","","","","","","","","","","","<code>Lose(n)</code> means the player will lose in <code>n</code> turns at most","","","","Cannot detect win or lose","","<code>Win(n)</code> means the player will win in <code>n</code> turns at least","","","","","","","","","","","","","","","","","","","Compare <code>value</code> and the value of <code>board</code>.","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","","Returns the argument unchanged.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","","","","","","","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","",""],"i":[19,0,0,0,0,0,0,0,0,19,0,0,14,0,0,0,0,0,0,15,16,0,0,0,17,19,15,19,9,15,14,14,16,9,0,17,9,0,0,19,16,0,19,1,2,0,4,32,29,33,30,34,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,32,29,33,30,34,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,6,6,5,5,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,0,73,10,12,13,5,5,5,6,2,1,9,5,5,1,6,9,11,14,5,15,16,17,19,1,0,2,9,10,11,12,13,14,5,5,6,2,15,16,4,4,17,18,19,20,1,32,29,33,30,34,9,10,11,12,13,14,5,6,6,6,6,2,15,16,4,17,18,19,20,1,4,9,6,6,6,6,9,11,14,5,15,16,17,19,1,11,11,12,13,2,32,29,33,30,34,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,32,29,33,30,34,10,12,13,18,20,73,10,12,13,5,5,4,12,13,17,19,5,4,5,73,10,12,13,18,20,5,5,5,1,6,2,4,32,29,33,30,34,18,20,18,20,4,17,18,20,5,4,5,5,5,5,5,9,5,6,6,6,4,4,2,9,2,11,18,20,4,0,0,1,5,5,0,5,5,5,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,5,9,5,4,5,0,0,32,29,33,30,34,9,10,11,12,13,14,5,6,6,2,15,16,4,17,18,19,20,1,6,32,29,33,30,34,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,32,29,33,30,34,9,10,11,12,13,14,5,6,2,15,16,4,17,18,19,20,1,11,11,4,2,2,2,0,7,0,40,7,0,0,35,39,41,42,42,39,39,41,42,42,0,35,0,38,40,40,7,40,42,40,40,35,39,39,35,27,0,27,0,40,40,40,42,35,38,7,39,40,27,41,42,35,38,7,39,40,27,41,42,35,38,7,39,40,27,41,42,35,38,7,39,40,27,41,42,35,35,38,38,7,7,39,40,27,27,41,42,35,38,7,39,40,27,41,42,35,38,7,39,40,27,41,42,35,38,7,27,35,38,7,39,40,27,41,42,35,38,7,27,35,38,7,39,40,27,41,42,35,38,7,39,40,27,41,42,35,38,7,39,40,27,41,42,74,75,76,77,76,78,79,80,44,0,0,44,0,0,0,0,0,44,0,0,0,0,0,46,45,0,0,46,45,46,45,0,44,45,46,50,51,44,45,46,50,51,44,45,46,44,45,46,0,44,44,45,46,50,51,44,45,46,50,50,51,44,45,46,50,51,50,51,50,50,51,50,51,44,50,50,44,45,46,44,44,45,46,50,51,44,45,46,50,51,50,51,44,45,46,50,51,81,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,53,54,55,55,53,54,53,54,53,54,64,66,59,57,67,62,68,55,53,69,58,63,56,70,61,71,54,64,66,59,57,67,62,68,55,53,69,58,63,56,70,61,71,54,53,54,53,54,55,53,54,55,53,54,53,54,55,53,54,53,54,53,54,53,54,55,53,54,64,66,59,57,67,62,68,55,53,53,69,58,63,56,70,61,71,54,53,54,53,54,53,54,64,66,59,57,67,62,68,55,53,69,58,63,56,70,61,71,54,64,66,59,57,67,62,68,53,69,58,63,56,70,61,71,54,53,53,54,55,53,54,53,54,53,54,53,54,55,53,54,53,54,53,54,55,53,54,64,66,59,57,67,62,68,69,58,63,56,70,61,71,53,53,53,54,53,54,53,54,53,54,53,54,53,54,53,54,53,54,55,53,54,64,66,59,57,67,62,68,55,53,69,58,63,56,70,61,71,54,64,66,59,57,67,62,68,55,53,69,58,63,56,70,61,71,54,64,66,59,57,67,62,68,55,53,69,58,63,56,70,61,71,54,53,54,53,54],"f":[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,[[1,1]],[2,3],0,[4,5],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[6,[[8,[5,7]]]],[6,5],[[5,9],[[8,[7]]]],[[5,9],[[8,[7]]]],[9,9],[10,10],[11,11],[12,12],[13,13],[14,14],[5,5],[6,6],[2,2],[15,15],[16,16],[4,4],[17,17],[18,18],[19,19],[20,20],[1,1],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[17,19],21],[9,3],[[10,19],3],[[12,9],3],[[13,9],3],[5,22],[[5,17],22],[[],5],[[],6],[[],2],0,[9,19],[[5,17],10],[[5,17],10],0,[[],6],[[9,9],3],[[11,11],3],[[14,14],3],[[5,5],3],[[15,15],3],[[16,16],3],[[17,17],3],[[19,19],3],[[1,1],3],0,[2,17],[[9,23],24],[[10,23],24],[[11,23],24],[[12,23],24],[[13,23],24],[[14,23],24],[[5,23],24],[[5,23],24],[[6,23],24],[[2,23],24],[[15,23],24],[[16,23],24],[[4,23],24],[[4,23],24],[[17,23],24],[[18,23],24],[[19,23],24],[[20,23],24],[[1,23],24],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[25,6],[[]],[[],6],[[],6],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[2,4],[[26,5],[[8,[9,27]]]],[26,[[8,[6]]]],[[],6],[25,6],[[],6],[[9,28]],[[11,28]],[[14,28]],[[5,28]],[[15,28]],[[16,28]],[[17,28]],[[19,28]],[[1,28]],0,0,[[12,22]],[[13,22]],[2,5],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[10],[12],[13],[[]],[[]],[[],3],[10,3],[12,3],[13,3],[[5,17,19],3],[[5,17,19],3],[4,3],[12,29],[13,30],[[],18],[[],20],[[5,17,3,3,3],12],[4,12],[[5,17,3,3,3],13],[[],22],[10,22],[12,22],[13,22],[18,22],[20,22],[[5,17,19],[[31,[22]]]],[[5,17],22],[5,11],[1],[[],6],[3,2],[3,4],[32,31],[29,31],[33,31],[30,31],[34,31],[18,31],[20,31],[18,31],[20,31],[4,17],[17],[[18,22],31],[[20,22],31],[[5,9],[[8,[7]]]],[[4,9],[[8,[35]]]],[[5,9],[[8,[7]]]],[[5,9],[[8,[5,7]]]],[[5,9],[[8,[5,7]]]],[[5,9]],[[5,9],5],[9,17],[[5,17,19],[[31,[1]]]],[6,6],[[6,22,22,17,19],6],[[6,17,19],6],[4],[4,2],[[2,3],2],[9,[[31,[1]]]],[2,15],0,[18],[20],[4,16],0,0,[[1,1]],[5,14],[5],0,[5],[5,36],[[5,17],25],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[5,21,26],36],[[9,5],[[8,[36,27]]]],[[],36],[[],36],[5,25],0,[21,31],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],[[8,[6]]]],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],[[8,[6,7]]]],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],0,0,[4,[[31,[17]]]],[[2,17],2],[[2,5],[[8,[2,38]]]],[[2,15],2],0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[35,35],[38,38],[7,7],[39,39],[40,40],[27,27],[41,41],[42,42],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[35,23],24],[[35,23],24],[[38,23],24],[[38,23],24],[[7,23],24],[[7,23],24],[[39,23],24],[[40,23],24],[[27,23],24],[[27,23],24],[[41,23],24],[[42,23],24],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[43],[43],[43],[43],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],36],[[],36],[[],36],[[],36],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[44,44],[45,45],[46,46],[[]],[[]],[[]],[[46,5,17,2],[[8,[47,44]]]],[[44,23],24],[[44,23],24],[[45,23],24],[[46,23],24],[[[50,[[0,[48,49]]]],23],24],[[[51,[[0,[48,49]]]],23],24],[[]],[[]],[[]],[[]],[[[51,[48]]],[[50,[48]]]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[[50,[48]]],[[51,[48]]]],[48,[[50,[48]]]],[48,[[51,[48]]]],[[[50,[48]]],31],[[[51,[48]]],31],[43],[[[50,[48]]],[[51,[48]]]],[[[50,[48]]],[[51,[48]]]],[[]],[[]],[[]],[[],36],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[[50,[48]]],[[52,[[31,[5]]]]]],[[[51,[48]]],[[52,[[31,[25]]]]]],[[],37],[[],37],[[],37],[[],37],[[],37],0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,[[53,53]],[[54,54]],[[55,55]],[[55,55]],[[53,53]],[[54,54]],[[53,53]],[[54,54]],[[53,53]],[[54,54]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[53,55],[54,55],[53],[54],[55,55],[53,53],[54,54],[[]],[[]],[[]],[[53,5],3],[[54,25],3],[[],55],[[],53],[[],54],[[53,53],56],[[54,54],57],[53,58],[54,59],[[53,60]],[[54,60]],[[55,23],24],[[53,23],24],[[54,23],24],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[54,53],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[60,53],[60,54],[[53,5]],[[54,25]],[[53,53],61],[[54,54],62],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[53],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[54],[53,54],[[53,53],3],[[54,54],3],[55,3],[53,3],[54,3],[[53,53],3],[[54,54],3],[[53,53],3],[[54,54],3],[53,63],[54,64],[55,22],[53,22],[54,22],[[53,48],52],[[54,48],52],[[53,48,65],52],[[54,48,65],52],[[],55],[[],53],[[],54],[64,31],[66,31],[59,31],[57,31],[67,31],[62,31],[68,31],[69,31],[58,31],[63,31],[56,31],[70,31],[61,31],[71,31],[53,54],[53,54],[[53,5],3],[[54,25],3],[48,55],[48,55],[[48,65],55],[[48,65],55],[[53,55]],[[54,55]],[[53,65]],[[54,65]],[[53,72],52],[[54,72],52],[[53,53],70],[[54,54],67],[[53,5],[[31,[5]]]],[[54,25],[[31,[25]]]],[[]],[[]],[[]],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],8],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[],37],[[53,53],71],[[54,54],68],[55,53],[55,54]],"c":[],"p":[[3,"Shift"],[3,"GameRule"],[15,"bool"],[3,"Game"],[3,"Board"],[3,"BoardBuilder"],[4,"BoardError"],[4,"Result"],[4,"Action"],[3,"DoveSet"],[3,"Rectangle"],[3,"ActionsFwd"],[3,"ActionsBwd"],[4,"SurroundedStatus"],[4,"WinnerJudgement"],[4,"GameStatus"],[4,"Color"],[3,"ColorIter"],[4,"Dove"],[3,"DoveIter"],[15,"char"],[15,"usize"],[3,"Formatter"],[6,"Result"],[15,"u64"],[15,"str"],[4,"ActionConvertError"],[8,"Hasher"],[3,"ActionsFwdIter"],[3,"ActionsBwdIter"],[4,"Option"],[3,"DoveSetIntoIter"],[3,"ActionsFwdIntoIter"],[3,"ActionsBwdIntoIter"],[4,"GameError"],[3,"String"],[3,"TypeId"],[4,"GameRuleError"],[4,"BoardCreateErrorType"],[4,"ActionPerformErrorType"],[4,"SSNEncodingErrorType"],[4,"SSNDecodingErrorType"],[3,"Demand"],[4,"CompareBoardValueError"],[4,"BoardValueErrorType"],[4,"BoardValue"],[15,"i8"],[8,"Read"],[8,"Debug"],[3,"LazyBoardLoader"],[3,"LazyRawBoardLoader"],[6,"Result"],[3,"BoardSet"],[3,"RawBoardSet"],[3,"Capacity"],[3,"Difference"],[3,"RawDifference"],[3,"Drain"],[3,"RawDrain"],[8,"IntoIterator"],[3,"Intersection"],[3,"RawIntersection"],[3,"Iter"],[3,"RawIter"],[8,"FnMut"],[3,"RawIntoIter"],[3,"RawSymmetricDifference"],[3,"RawUnion"],[3,"IntoIter"],[3,"SymmetricDifference"],[3,"Union"],[8,"Write"],[8,"ActionContainer"],[13,"SSNEncodingError"],[13,"SSNDecodingError"],[13,"ActionPerformError"],[13,"BoardCreateError"],[13,"ProhibitedRemoveError"],[13,"BoardError"],[13,"GameFinishedError"],[13,"BoardValueError"]]}\
}');
if (typeof window !== 'undefined' && window.initSearch) {window.initSearch(searchIndex)};
if (typeof exports !== 'undefined') {exports.searchIndex = searchIndex};
