</
  define p: output$=23;
  define q: output$=21;
  define r: output$=24;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>