// #include "sparrow_multiplexer.h"

struct sparrow_multiplexer_t {
  int sequenced; //Boolean indicating whether we have a single sequence of communication or multiple.
  int allInOneGo;  //All-in-one-go multiplexers are agnostic. IMPORTANT : One step before the subgraph starts, all other paths are
  // suspended till this subgraph finishes. This way, we do not require a signal to be transmitted to initiate the allinonego subgraph, 
  // allowing our library to be used to implement all types of protocols. (that do not have that signal).
  int agnostic; // It requires allInOneGo. It puts the continuation state inside the data.
  //We need to be able to represent the graph of interactions that this multiplexer represents as well as the position that it currently is.
  //We also need to have a way that other multiplexers can make requests to this multiplexer without knowing whether it is the multiplexer or the sparrow buffer. Timeouts need to be given to the multiplexer that made them so as to handle them as they see fit.
  //That could produce a hierarchy of timeouts.
  int persistent; //Needed for multi-party protocols to guarantee agent-consistency.
};




