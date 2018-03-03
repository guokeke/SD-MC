</
  define p: output$=21;
  define q: output$=23;
  define r: output$=26;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>