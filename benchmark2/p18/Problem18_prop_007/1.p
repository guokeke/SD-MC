</
  define p: input$=1;
  define q: input$=6;
  define r: output$=22;
  
  alw(!(p and !q and som(q)) or (alw(!r);next q))
/>