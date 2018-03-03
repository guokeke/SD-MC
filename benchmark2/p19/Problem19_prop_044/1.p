</
  define p: output$=26;
  define q: input$=2;
  define r: output$=21;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>