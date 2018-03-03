</
  define p: output$=22;
  define q: input$=5;
  define r: output$=25;
  
  alw(!(p or !q and som(q)) or (alw(!r);next q))
/>
