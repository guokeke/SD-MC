</
  define p: input$=2;
  define q: output$=26;
  define r: output$=22;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>