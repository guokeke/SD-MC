</
  define p: output$=21;
  define q: output$=26;
  define r: output$=23;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>
