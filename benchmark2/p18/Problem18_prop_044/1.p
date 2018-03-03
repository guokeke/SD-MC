</
  define p: output$=24;
  define q: input$=6;
  define r: output$=26;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>